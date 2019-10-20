-module(least_upper_bound).
-include("typelib.hrl").
-import(typelib, [type/2, type/1]).

-export([normalize/2]).

%% Normalize
%% ---------
%%
%% * Expand user-defined and remote types on head level (except opaque types)
%% * Replace built-in type synonyms
%% * Flatten unions and merge overlapping types (e.g. ranges) in unions

-spec normalize(type(), TEnv :: #tenv{}) -> type().
normalize({type, _, union, Tys}, TEnv) ->
    Types = flatten_unions(Tys, TEnv),
    case merge_union_types(Types, TEnv) of
        []  -> type(none);
        [T] -> T;
        Ts  -> type(union, Ts)
    end;
normalize({user_type, P, Name, Args} = Type, TEnv) ->
    case typelib:get_module_from_annotation(P) of
        {ok, Module} ->
            %% Local type in another module, from an expanded remote type
            case gradualizer_db:get_type(Module, Name, Args) of
                {ok, T} ->
                    normalize(T, TEnv);
                opaque ->
                    Type;
                not_found ->
                    throw({undef, user_type, P, {Module, Name, length(Args)}})
            end;
        none ->
            %% Local user-defined type
            TypeId = {Name, length(Args)},
            case TEnv#tenv.types of
                #{TypeId := {Vars, Type0}} ->
                    VarMap = maps:from_list(lists:zip(Vars, Args)),
                    Type1 = typelib:substitute_type_vars(Type0, VarMap),
                    normalize(Type1, TEnv);
                _NotFound ->
                    throw({undef, user_type, P, {Name, length(Args)}})
            end
    end;
normalize({remote_type, P, [{atom, _, M} = Module, {atom, _, N} = Name, Args]}, TEnv) ->
    case gradualizer_db:get_exported_type(M, N, Args) of
        {ok, T} ->
            normalize(T, TEnv);
        opaque ->
            typelib:annotate_user_types(M, {user_type, P, N, Args});
        not_exported ->
            throw({not_exported, remote_type, {Module, Name, length(Args)}});
        not_found ->
            throw({undef, remote_type, {Module, Name, length(Args)}})
    end;
normalize({op, _, _, _Arg} = Op, _TEnv) ->
    erl_eval:partial_eval(Op);
normalize({op, _, _, _Arg1, _Arg2} = Op, _TEnv) ->
    erl_eval:partial_eval(Op);
normalize({type, Ann, range, [T1, T2]}, TEnv) ->
    {type, Ann, range, [normalize(T1, TEnv), normalize(T2, TEnv)]};
normalize(Type, _TEnv) ->
    expand_builtin_aliases(Type).

%% Replace built-in type aliases
-spec expand_builtin_aliases(type()) -> type().
expand_builtin_aliases({var, Ann, '_'}) ->
    {type, Ann, any, []};
expand_builtin_aliases({type, Ann, binary, []}) ->
    {type, Ann, binary, [{integer, Ann, 0}, {integer, Ann, 8}]};
expand_builtin_aliases({type, Ann, bitstring, []}) ->
    {type, Ann, binary, [{integer, Ann, 0}, {integer, Ann, 1}]};
expand_builtin_aliases({type, Ann, boolean, []}) ->
    {type, Ann, union, [{atom, Ann, true}, {atom, Ann, false}]};
expand_builtin_aliases({type, Ann, bool, []}) ->
    {type, Ann, union, [{atom, Ann, true}, {atom, Ann, false}]};
expand_builtin_aliases({type, Ann, byte, []}) ->
    {type, Ann, range, [{integer, Ann, 0}, {integer, Ann, 255}]};
expand_builtin_aliases({type, Ann, char, []}) ->
    {type, Ann, range, [{integer, Ann, 0}, {integer, Ann, 16#10ffff}]};
expand_builtin_aliases({type, Ann, number, []}) ->
    {type, Ann, union, [{type, Ann, integer, []}, {type, Ann, float, []}]};
expand_builtin_aliases({type, Ann, list, []}) ->
    {type, Ann, list, [{type, Ann, any, []}]};
expand_builtin_aliases({type, Ann, maybe_improper_list, []}) ->
    {type, Ann, maybe_improper_list, [{type, Ann, any, []},
                                      {type, Ann, any, []}]};
expand_builtin_aliases({type, Ann, nonempty_list, []}) ->
    {type, Ann, nonempty_list, [{type, Ann, any, []}]};
expand_builtin_aliases({type, Ann, string, []}) ->
    {type, Ann, list, [{type, Ann, char, []}]};
expand_builtin_aliases({type, Ann, nonempty_string, []}) ->
    {type, Ann, nonempty_list, [{type, Ann, char, []}]};
expand_builtin_aliases({type, Ann, iodata, []}) ->
    {type, Ann, union, [{type, Ann, iolist, []}, {type, Ann, binary, []}]};
expand_builtin_aliases({type, Ann, iolist, []}) ->
    %% recursive type
    Union = [{type, Ann, byte, []},
             {type, Ann, binary, []},
             {type, Ann, iolist, []}],
    Tail = [{type, Ann, nil, []},
            {type, Ann, binary, []}],
    {type, Ann, maybe_improper_list, [{type, Ann, union, Union},
                                      {type, Ann, union, Tail}]};
expand_builtin_aliases({type, Ann, function, []}) ->
    {type, Ann, 'fun', [{type, Ann, any}, {type, Ann , any,[]}]};
expand_builtin_aliases({type, Ann, 'fun', []}) ->
    %% `fun()' is not a built-in alias per the erlang docs
    %% but it is equivalent with `fun((...) -> any())'
    {type, Ann, 'fun', [{type, Ann, any}, {type, Ann, any, []}]};
expand_builtin_aliases({type, Ann, module, []}) ->
    {type, Ann, atom, []};
expand_builtin_aliases({type, Ann, mfa, []}) ->
    {type, Ann, tuple, [{type, Ann, module, []},
                        {type, Ann, atom, []},
                        {type, Ann, arity, []}]};
expand_builtin_aliases({type, Ann, arity, []}) ->
    {type, Ann, range, [{integer, Ann, 0}, {integer, Ann, 255}]};
expand_builtin_aliases({type, Ann, identifier, []}) ->
    {type, Ann, union, [{type, Ann, pid, []},
                        {type, Ann, port, []},
                        {type, Ann, reference, []}]};
expand_builtin_aliases({type, Ann, node, []}) ->
    {type, Ann, atom, []};
expand_builtin_aliases({type, Ann, timeout, []}) ->
    {type, Ann, union, [{atom, Ann, infinity},
                        {type, Ann, non_neg_integer, []}]};
expand_builtin_aliases({type, Ann, no_return, []}) ->
    {type, Ann, none, []};
expand_builtin_aliases(Type) ->
    Type.

%% Flattens nested unions
%%
%% Mutually recursive with normalize/2
%%
%% * Normalize each element
%% * TODO: Detect user-defined and remote types expanding to themselves
%%   or to unions containing themselves (using memoization?)
%% * Remove subtypes of other types in the same union; keeping any() separate
%% * Merge integer types, including singleton integers and ranges
%%   1, 1..5, integer(), non_neg_integer(), pos_integer(), neg_integer()
-spec flatten_unions([type()], #tenv{}) -> [type()].
flatten_unions(Tys, TEnv) ->
    [ FTy || Ty <- Tys, FTy <- flatten_type(normalize(Ty, TEnv), TEnv) ].

flatten_type({type, _, none, []}, _) ->
    [];
flatten_type({type, _, union, Tys}, TEnv) ->
    flatten_unions(Tys, TEnv);
flatten_type({ann_type, _, [_, Ty]}, TEnv) ->
    flatten_type(normalize(Ty, TEnv), TEnv);
flatten_type(Ty, _TEnv) ->
    [Ty].

%% Merges overlapping integer types (including ranges and singletons).
%% (TODO) Removes all types that are subtypes of other types in the same union.
%% Retuns a list of disjoint types.
merge_union_types(Types, _TEnv) ->
    case lists:any(fun ({type, _, term, []}) -> true; (_) -> false end,
                   Types) of
        true ->
            %% term() is among the types.
            [type(term)];
        false ->
            {IntegerTypes1, OtherTypes1} =
            lists:partition(fun type_integer:is_int_type/1, Types),
            IntegerTypes2 = type_integer:merge_int_types(IntegerTypes1),
            OtherTypes2 = merge_atom_types(OtherTypes1),
            OtherTypes3 = lists:usort(OtherTypes2),
            IntegerTypes2 ++ OtherTypes3
    end.


%% Remove all atom listerals if atom() is among the types.
merge_atom_types(Types) ->
    IsAnyAtom = lists:any(fun ({type, _, atom, []}) -> true;
                              (_)                   -> false
                          end,
                          Types),
    if
        IsAnyAtom -> lists:filter(fun ({atom, _, _}) -> false;
                                      (_)            -> true
                                  end,
                                  Types);
        true      -> Types
    end.
