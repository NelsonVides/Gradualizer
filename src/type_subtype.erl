-module(type_subtype).
-include("typelib.hrl").
-import(typelib, [ret/1, get_record_fields/3]).

-export([
         subtype/3,
         any_subtype/3,
         compat_tys/4
        ]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Subtyping compatibility
%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% The first argument is a "compatible subtype" of the second.

-spec subtype(type(), type(), #tenv{}) -> {true, any()} | false.
subtype(Ty1, Ty2, TEnv) ->
    try compat(Ty1, Ty2, sets:new(), TEnv) of
        {_Memoization, Constraints} ->
            {true, Constraints}
    catch
        nomatch ->
            false
    end.

%% Check if at least on of the types in a list is a subtype of a type.
%% Used when checking intersection types.
any_subtype([], _Ty, _TEnv) ->
    false;
any_subtype([Ty1|Tys], Ty, TEnv) ->
    case subtype(Ty1, Ty, TEnv) of
        R={true, _} ->
            R;
        false ->
            any_subtype(Tys, Ty, TEnv)
    end.


% This function throws an exception in case of a type error

%% The functions compat and compat_ty are mutually recursive.
%% The main entry point is compat and all recursive calls should go via compat.
%% The function compat_ty is just a convenience function to be able to
%% pattern match on types in a nice way.
compat(T1, T2, A, TEnv) ->
    Ty1 = typelib:remove_pos(least_upper_bound:normalize(T1, TEnv)),
    Ty2 = typelib:remove_pos(least_upper_bound:normalize(T2, TEnv)),
    case sets:is_element({Ty1, Ty2}, A) of
        true ->
            ret(A);
        false ->
            compat_ty(Ty1, Ty2, sets:add_element({Ty1, Ty2}, A), TEnv)
    end.

%% any() is used as the unknown type in the gradual type system
compat_ty({type, _, any, []}, _, A, _TEnv) ->
    ret(A);
compat_ty(_, {type, _, any ,[]}, A, _TEnv) ->
    ret(A);
%% Term is the top of the subtyping relation
compat_ty(_, {type, _, term, []}, A, _TEnv) ->
    ret(A);
%% None is the bottom of the subtyping relation
compat_ty({type, _, none, []}, _, A, _TEnv) ->
    ret(A);
%% Every type is subtype of itself
compat_ty(T, T, A, _TEnv) ->
    ret(A);

%% Variables
compat_ty({var, _, Var}, Ty, A, _TEnv) ->
    {A, constraints:upper(Var, Ty)};
compat_ty(Ty, {var, _, Var}, A, _TEnv) ->
    {A, constraints:lower(Var, Ty)};
compat_ty({ann_type, _, [{var, _, Var}, Ty1]}, Ty2, A, TEnv) ->
    {A1, Cs} = compat(Ty1, Ty2, A, TEnv),
    {A1, constraints:combine(Cs, constraints:upper(Var, Ty1))};
compat_ty(Ty1, {ann_type, _, [{var, _, Var}, Ty2]}, A, TEnv) ->
    {A1, Cs} = compat(Ty1, Ty2, A, TEnv),
    {A1, constraints:combine(Cs, constraints:upper(Var, Ty2))};



% TODO: There are several kinds of fun types.
% Add support for them all eventually
compat_ty({type, _, 'fun', [_, Res1]},
          {type, _, 'fun', [{type, _, any}, Res2]},
          A, TEnv) ->
    compat(Res1, Res2, A, TEnv);
compat_ty({type, _, 'fun', [{type, _, product, Args1}, Res1]},
          {type, _, 'fun', [{type, _, product, Args2}, Res2]},
          A, TEnv) ->
    {Ap, Cs} = compat_tys(Args2, Args1, A, TEnv),
    {Aps, Css} = compat(Res1, Res2, Ap, TEnv),
    {Aps, constraints:combine(Cs, Css)};

%% Unions
compat_ty({type, _, union, Tys1}, {type, _, union, Tys2}, A, TEnv) ->
    lists:foldl(fun (Ty1, {A1, C1}) ->
                    {A2, C2} = any_type(Ty1, Tys2, A1, TEnv),
                    {A2, constraints:combine(C1, C2)}
                end, {A, constraints:empty()}, Tys1);
compat_ty(Ty1, {type, _, union, Tys2}, A, TEnv) ->
    any_type(Ty1, Tys2, A, TEnv);
compat_ty({type, _, union, Tys1}, Ty2, A, TEnv) ->
    all_type(Tys1, Ty2, A, TEnv);

% Integer types
compat_ty(Ty1, Ty2, A, _TEnv) when ?is_int_type(Ty1), ?is_int_type(Ty2) ->
    R1 = type_integer:int_type_to_range(Ty1),
    R2 = type_integer:int_type_to_range(Ty2),
    case type_integer:lower_bound_less_or_eq(R2, R1) andalso
        type_integer:upper_bound_more_or_eq(R2, R1) of
        true -> ret(A);
        false -> throw(nomatch)
    end;

%% Atoms
compat_ty({atom, _, _Atom}, {type, _, atom, []}, A, _TEnv) ->
    ret(A);

%% Binary, bitstring
%%
%% <<_:M, _:_*N>> means
%% a bitstring with bit size M + K*N (for any K)
%%
%% <<_:M1, _:_*N1>> is subtype of <<_:M2, _:_*N2>> if
%% for all K, there is an L such that
%% M1 + K*N1 == M2 + L*N2
%%
%%                 M1      M1+N1   M1+2*N1
%% T1 .............|.......|.......|...
%% T2 .....|...|...|...|...|...|...|...
%%         M2      M2+L*N2
%%
compat_ty({type, _, binary, [{integer, _, M1}, {integer, _, N1}]},
          {type, _, binary, [{integer, _, M2}, {integer, _, N2}]},
          A, _TEnv)
  when N2 > 0, M1 >= M2,
       N1 rem N2 == 0,
       (M1 - M2) rem N2 == 0 ->
    ret(A);

%% Records with the same name, defined in differend modules
%% TODO: Record equivallend on tuple form
compat_ty({type, P1, record, [{atom, _, Name}]},
          {type, P2, record, [{atom, _, Name}]}, A, TEnv) ->
    Fields1 = get_maybe_remote_record_fields(Name, P1, TEnv),
    Fields2 = get_maybe_remote_record_fields(Name, P2, TEnv),
    compat_record_fields(Fields1, Fields2, A, TEnv);

compat_ty({type, _, record, _}, {type, _, tuple, any}, A, _TEnv) ->
    ret(A);

%% Lists
compat_ty(Ty1, Ty2, A, TEnv) when ?is_list_type(Ty1), ?is_list_type(Ty2) ->
    {Empty1, Elem1, Term1} = typelib:list_view(Ty1),
    {Empty2, Elem2, Term2} = typelib:list_view(Ty2),
    case {Empty1, Empty2} of
        {E, E}   -> ok;
        {_, any} -> ok;
        _        -> throw(nomatch)
    end,
    compat_tys([Elem1, Term1], [Elem2, Term2], A, TEnv);

%% Tuples
compat_ty({type, _, tuple, any}, {type, _, tuple, _Args}, A, _TEnv) ->
    ret(A);
compat_ty({type, _, tuple, _Args}, {type, _, tuple, any}, A, _TEnv) ->
    ret(A);
compat_ty({type, _, tuple, Args1}, {type, _, tuple, Args2}, A, TEnv) ->
    compat_tys(Args1, Args2, A, TEnv);
%compat_ty({user_type, _, Name, Args}, Ty, A, TEnv) ->
%    compat(unfold_user_type(Name, Args, TEnv), Ty, A, TEnv);

%% Maps
compat_ty({type, _, map, any}, {type, _, map, _Assocs}, A, _TEnv) ->
    ret(A);
compat_ty({type, _, map, _Assocs}, {type, _, map, any}, A, _TEnv) ->
    ret(A);
compat_ty({type, _, map, Assocs1}, {type, _, map, Assocs2}, A, TEnv) ->
    lists:foldl(fun (Assoc2, {As, Cs1}) ->
			begin
			    {Ax, Cs2} = any_type(Assoc2, Assocs1, As, TEnv),
			    {Ax, constraints:combine(Cs1, Cs2)}
			end
		end, ret(A), Assocs2);
compat_ty({type, _, AssocTag2, [Key2, Val2]},
          {type, _, AssocTag1, [Key1, Val1]}, A, TEnv)
        when AssocTag2 == map_field_assoc, AssocTag1 == map_field_assoc;
             AssocTag2 == map_field_exact, AssocTag1 == map_field_exact;
             AssocTag2 == map_field_assoc, AssocTag1 == map_field_exact ->
    %% For M1 <: M2, mandatory fields in M2 must be mandatory fields in M1
    {A1, Cs1} = compat_ty(Key1, Key2, A, TEnv),
    {A2, Cs2} = compat_ty(Val1, Val2, A1, TEnv),
    {A2, constraints:combine(Cs1, Cs2)};

compat_ty(_Ty1, _Ty2, _, _) ->
    throw(nomatch).

compat_tys([], [], A, _TEnv) ->
    ret(A);
compat_tys([Ty1|Tys1], [Ty2|Tys2], A, TEnv) ->
    {Ap, Cs} =
    compat(Ty1 ,Ty2, A, TEnv),
    {Aps, Css} = compat_tys(Tys1, Tys2, Ap, TEnv),
    {Aps, constraints:combine(Cs, Css)};
compat_tys(_Tys1, _Tys2, _, _) ->
    throw(nomatch).

%% Two records are compatible if they have the same name (defined in different
%% modules) and they have the same number of fields and the field types match.
compat_record_fields([], [], A, _TEnv) ->
    ret(A);
compat_record_fields([{typed_record_field, _NameAndDefaultValue1, T1} | Fs1],
                     [{typed_record_field, _NameAndDefaultValue2, T2} | Fs2],
                     A, TEnv) ->
    {A1, Cs1} = compat(T1, T2, A, TEnv),
    {A2, Cs2} = compat_record_fields(Fs1, Fs2, A1, TEnv),
    {A2, constraints:combine(Cs1, Cs2)};
compat_record_fields(_, _, _, _) ->
    %% Mismatching number of fields
    throw(nomatch).

any_type(_Ty, [], _A, _TEnv) ->
    throw(nomatch);
any_type(Ty, [Ty1|Tys], A, TEnv) ->
    try
        compat(Ty, Ty1, A, TEnv)
    catch
        nomatch ->
            any_type(Ty, Tys, A, TEnv)
    end.

%% @doc All types in `Tys' must be compatible with `Ty'.
%% Returns all the gather memoizations and constrains.
%% Does not return (throws `nomatch') if any of the types is not compatible.
all_type(Tys, Ty, A, TEnv) ->
    all_type(Tys, Ty, A, [], TEnv).

all_type([], _Ty, A, Css, _TEnv) ->
    {A, constraints:combine(Css)};
all_type([Ty1|Tys], Ty, AIn, Css, TEnv) ->
    {AOut, Cs} = compat_ty(Ty1, Ty, AIn, TEnv),
    all_type(Tys, Ty, AOut, [Cs|Css], TEnv).

get_maybe_remote_record_fields(RecName, Anno, TEnv) ->
    case typelib:get_module_from_annotation(Anno) of
        {ok, Module} ->
            %% A record type in another module, from an expanded remote type
            case gradualizer_db:get_record_type(Module, RecName) of
                {ok, TypedRecordFields} ->
                    TypedRecordFields;
                not_found ->
                    throw({undef, record, Anno, {Module, RecName}})
            end;
        none ->
            %% Local record type
            get_record_fields(RecName, Anno, TEnv)
    end.

%% End of subtype help functions

