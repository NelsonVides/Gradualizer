-module(greatest_lower_bound).
-include("typelib.hrl").
-import(typelib,
        [type/2,
         type/1,
         ret/1,
         new_type_var/0,
         list_view/1,
         from_list_view/1
        ]).

-export([glb/3, glb/2]).

%% Greatest lower bound
%% --------------------
%%
%% * Computes the maximal (in the subtyping hierarchy) type that is a subtype
%%   of two given types.

-spec glb(type(), type(), TEnv :: #tenv{}) -> {type(), constraints:constraints()}.
glb(T1, T2, TEnv) ->
    glb(T1, T2, #{}, TEnv).

-spec glb([type()], TEnv :: #tenv{}) -> {type(), constraints:constraints()}.
glb(Ts, TEnv) ->
    lists:foldl(fun (T, {TyAcc, Cs1}) ->
                        {Ty, Cs2} = glb(T, TyAcc, TEnv),
                        {Ty, constraints:combine(Cs1, Cs2)}
                end,
                {type(term), constraints:empty()},
                Ts).

glb(T1, T2, A, TEnv) ->
    case maps:is_key({T1, T2}, A) of
        %% If we hit a recursive case we approximate with none(). Conceivably
        %% you could do some fixed point iteration here, but let's wait for an
        %% actual use case.
        true -> {type(none), constraints:empty()};
        false ->
            case gradualizer_cache:get_glb(TEnv#tenv.module, T1, T2) of
                false ->
                    Ty1 = typelib:remove_pos(least_upper_bound:normalize(T1, TEnv)),
                    Ty2 = typelib:remove_pos(least_upper_bound:normalize(T2, TEnv)),
                    {Ty, Cs} = glb_ty(Ty1, Ty2, A#{ {Ty1, Ty2} => 0 }, TEnv),
                    NormTy = least_upper_bound:normalize(Ty, TEnv),
                    gradualizer_cache:store_glb(TEnv#tenv.module, T1, T2, {NormTy, Cs}),
                    {NormTy, Cs};
                TyCs ->
                    %% these two types have already been seen and calculated
                    TyCs
            end
    end.

%% If either type is any() we don't know anything
glb_ty({type, _, any, []} = Ty1, _Ty2, _A, _TEnv) ->
    ret(Ty1);
glb_ty(_Ty1, {type, _, any, []} = Ty2, _A, _TEnv) ->
    ret(Ty2);

%% term() is the top of the hierarchy
glb_ty({type, _, term, []}, Ty2, _A, _TEnv) ->
    ret(Ty2);
glb_ty(Ty1, {type, _, term, []}, _A, _TEnv) ->
    ret(Ty1);

%% none() is the bottom of the hierarchy
glb_ty({type, _, none, []} = Ty1, _Ty2, _A, _TEnv) ->
    ret(Ty1);
glb_ty(_Ty1, {type, _, none, []} = Ty2, _A, _TEnv) ->
    ret(Ty2);

%% glb is idempotent
glb_ty(Ty, Ty, _A, _TEnv) ->
    ret(Ty);

%% Type variables. TODO: can we get here with constrained type variables?
glb_ty({ann_type, _, [{var, _, _}, Ty1]}, Ty2, A, TEnv) ->
    glb(Ty1, Ty2, A, TEnv);
glb_ty(Ty1, {ann_type, _, [{var, _, _}, Ty2]}, A, TEnv) ->
    glb(Ty1, Ty2, A, TEnv);
glb_ty(Var = {var, _, _}, Ty2, _A, _TEnv) ->
    V = new_type_var(),
    {{var, erl_anno:new(0), V}
    ,constraints:add_var(V,
       constraints:combine(
	 constraints:upper(V, Var),
	 constraints:upper(V, Ty2)
	))};
glb_ty(Ty1, Var = {var, _, _}, _A, _TEnv) ->
    V = new_type_var(),
    {{var, erl_anno:new(0), V}
    ,constraints:add_var(V,
       constraints:combine(
	 constraints:upper(V, Var),
	 constraints:upper(V, Ty1)
	))};

%% Union types: glb distributes over unions
glb_ty({type, Ann, union, Ty1s}, Ty2, A, TEnv) ->
    {Tys, Css} = lists:unzip([ glb_ty(Ty1, Ty2, A, TEnv) || Ty1 <- Ty1s ]),
    {{type, Ann, union, Tys}, constraints:combine(Css)};
glb_ty(Ty1, {type, Ann, union, Ty2s}, A, TEnv) ->
    {Tys, Css} = lists:unzip([glb_ty(Ty1, Ty2, A, TEnv) || Ty2 <- Ty2s ]),
    {{type, Ann, union, Tys}, constraints:combine(Css)};

%% Atom types
glb_ty(Ty1 = {atom, _, _}, {type, _, atom, []}, _A, _TEnv) ->
    ret(Ty1);
glb_ty({type, _, atom, []}, Ty2 = {atom, _, _}, _A, _TEnv) ->
    ret(Ty2);

%% Number types
glb_ty(Ty1, Ty2, _A, _TEnv) when ?is_int_type(Ty1), ?is_int_type(Ty2) ->
    {Lo1, Hi1} = type_integer:int_type_to_range(Ty1),
    {Lo2, Hi2} = type_integer:int_type_to_range(Ty2),
    ret(type(union, type_integer:int_range_to_types({type_integer:int_max(Lo1, Lo2), type_integer:int_min(Hi1, Hi2)})));

%% List types
glb_ty(Ty1, Ty2, A, TEnv) when ?is_list_type(Ty1), ?is_list_type(Ty2) ->
    {Empty1, Elem1, Term1} = list_view(Ty1),
    {Empty2, Elem2, Term2} = list_view(Ty2),
    Empty =
        case {Empty1, Empty2} of
            {E, E}            -> E;
            {any, E}          -> E;
            {E, any}          -> E;
            {empty, nonempty} -> none;
            {nonempty, empty} -> none
        end,
    {Elem, Cs1} = glb(Elem1, Elem2, A, TEnv),
    {Term, Cs2} = glb(Term1, Term2, A, TEnv),
    {from_list_view({Empty, Elem, Term}), constraints:combine(Cs1, Cs2)};

%% Tuple types
glb_ty(Ty1 = {type, _, tuple, Tys1}, Ty2 = {type, _, tuple, Tys2}, A, TEnv) ->
    case {Tys1, Tys2} of
        {any, _} -> ret(Ty2);
        {_, any} -> ret(Ty1);
        _ when length(Tys1) /= length(Tys2) -> ret(type(none));
        _ ->
	    {Tys, Css} =
		lists:unzip(lists:zipwith(fun(T1, T2) ->
						  glb(T1, T2, A, TEnv)
					  end,
					  Tys1, Tys2)),
            TupleType =
                case lists:any(fun(?type(none)) -> true; (_) -> false end,
                               Tys) of
                    true ->
                        type(none);
                    false ->
                        type(tuple, Tys)
                end,
	    {TupleType, constraints:combine(Css)}
    end;

%% Record types. Either exactly the same record (handled above) or tuple().
glb_ty(Ty1 = {type, _, record, _}, {type, _, tuple, any}, _A, _TEnv) ->
    ret(Ty1);
glb_ty({type, _, tuple, any}, Ty2 = {type, _, record, _}, _A, _TEnv) ->
    ret(Ty2);
glb_ty({type, _, record, _}, {type, _, record, _}, _A, _TEnv) ->
    ret(type(none));

%% Map types. These are a bit tricky and we can't reach this case in the
%% current code. For now going with a very crude approximation.
glb_ty(Ty1 = {type, _, map, Assocs1}, Ty2 = {type, _, map, Assocs2}, _A, _TEnv) ->
    case {Assocs1, Assocs2} of
        {any, _} -> ret(Ty2);
        {_, any} -> ret(Ty1);
        _        -> ret(type(none))
    end;

%% Binary types. For now approximate this by returning the smallest type if
%% they are comparable, otherwise none(). See the corresponding case in
%% compat_ty for the subtyping rule.
glb_ty(Ty1 = {type, _, binary, _},
       Ty2 = {type, _, binary, _}, _A, TEnv) ->
    case type_subtype:subtype(Ty1, Ty2, TEnv) of
        {true, _} -> ret(Ty1);    %% Will never produce constraints
        false ->
            case type_subtype:subtype(Ty2, Ty1, TEnv) of
                {true, _} -> ret(Ty2);
                false     -> ret(type(none))
            end
    end;

%% Function types. Would require lub on arguments for proper implementation.
%% For now pick biggest arguments when comparable and none() otherwise.
glb_ty({type, _, 'fun', [{type, _, product, Args1}, Res1]},
       {type, _, 'fun', [{type, _, product, Args2}, Res2]}, A, TEnv) ->
    NoConstraints = constraints:empty(),
    {Res, Cs} = glb(Res1, Res2, A, TEnv),
    Subtype =
        fun(Ts1, Ts2) ->
            try type_subtype:compat_tys(Ts1, Ts2, sets:new(), TEnv) of
                {_, NoConstraints} -> true;
                _ -> false
            catch throw:nomatch -> false end
        end,
    case Subtype(Args1, Args2) of
        true  -> {type('fun', [type(product, Args2), Res]), Cs};
        false ->
            case Subtype(Args2, Args1) of
                true  -> {type('fun', [type(product, Args1), Res]), Cs};
                false -> {type(none), Cs}
            end
    end;
glb_ty({type, _, 'fun', [{type, _, any} = Any, Res1]},
       {type, _, 'fun', [{type, _, any}, Res2]}, A, TEnv) ->
    {Res, Cs} = glb(Res1, Res2, A, TEnv),
    {type('fun', [Any, Res]), Cs};

glb_ty({type, _, 'fun', [{type, _, any}, Res1]},
       {type, _, 'fun', [{type, _, product, _} = TArgs2, _]} = T2, A, TEnv) ->
    glb_ty(type('fun', [TArgs2, Res1]), T2, A, TEnv);
glb_ty({type, _, 'fun', [{type, _, product, _} = TArgs1, _]} = T1,
       {type, _, 'fun', [{type, _, any}, Res2]}, A, TEnv) ->
    glb_ty(T1, type('fun', [TArgs1, Res2]), A, TEnv);

%% normalize and remove_pos only does the top layer
glb_ty({type, _, Name, Args1}, {type, _, Name, Args2}, A, TEnv)
        when length(Args1) == length(Args2) ->
    {Args, Css} = lists:unzip([ glb(Arg1, Arg2, A, TEnv) || {Arg1, Arg2} <- lists:zip(Args1, Args2) ]),
    {type(Name, Args), constraints:combine(Css)};

%% Incompatible
glb_ty(_Ty1, _Ty2, _A, _TEnv) -> {type(none), constraints:empty()}.
