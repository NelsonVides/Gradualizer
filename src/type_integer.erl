-module(type_integer).
-include("typelib.hrl").
-import(typelib, [type/1, type/2]).

-export([
         is_int_type/1,
         merge_int_types/1,
         int_type_to_range/1,
         int_range_to_types/1,
         negate_num_type/1,
         upper_bound_more_or_eq/2,
         lower_bound_less_or_eq/2
        ]).
-export([
         int_max/2,
         int_min/2,
         int_negate/1
        ]).

%% A type used while normalizing integer types. The ranges that are possible to
%% write in the type system, i.e. non_neg_integer(), pos_integer(),
%% neg_integer(), integer(), finite ranges, singletons and unions of these.
-type int_range() :: {neg_inf, -1 | non_neg_integer() | pos_inf} |
                     {neg_integer() | 0 | 1, pos_inf} |
                     {integer(), integer()}.

-export_type([int_range/0]).

-spec is_int_type(type()) -> boolean().
is_int_type({type, _, T, _})
  when T == pos_integer; T == non_neg_integer; T == neg_integer;
       T == integer; T == range -> true;
is_int_type({integer, _, _}) -> true;
is_int_type({char, _, _}) -> true;
is_int_type(_) -> false.

%% Merges integer types by sorting on the lower bound and then merging adjacent
%% ranges. Returns a list of mutually exclusive integer types.
%%
%% This is an adoption of the standard algorithm for merging intervals.
-spec merge_int_types([type()]) -> [type()].
merge_int_types([]) ->
    [];
merge_int_types(IntTypes) ->
    Ranges = lists:map(fun type_integer:int_type_to_range/1, IntTypes),
    [T | Ts] = lists:sort(fun lower_bound_less_or_eq/2, Ranges),
    MergedRanges = merge_int_ranges_help(Ts, [T]),
    lists:append(lists:map(fun int_range_to_types/1, MergedRanges)).

merge_int_ranges_help([{R1, R2} = R | Rs], [{S1, S2} | StackTail] = Stack) ->
    NewStack = if
                   R1 == neg_inf; S2 == pos_inf; R1 =< S2 + 1 ->
                       %% Overlapping or adjacent ranges. Merge them.
                       [{S1, int_max(R2, S2)} | StackTail];
                   true ->
                       %% Not mergeable ranges. Push R to stack.
                       [R | Stack]
               end,
    merge_int_ranges_help(Rs, NewStack);
merge_int_ranges_help([], Stack) ->
    lists:reverse(Stack).

%% Integer type to range, where the bounds can be infinities in some cases.
-spec int_type_to_range(type()) -> int_range().
int_type_to_range({type, _, integer, []})              -> {neg_inf, pos_inf};
int_type_to_range({type, _, neg_integer, []})          -> {neg_inf, -1};
int_type_to_range({type, _, non_neg_integer, []})      -> {0, pos_inf};
int_type_to_range({type, _, pos_integer, []})          -> {1, pos_inf};
int_type_to_range({type, _, range, [{Tag1, _, I1}, {Tag2, _, I2}]})
  when Tag1 =:= integer orelse Tag1 =:= char,
       Tag2 =:= integer orelse Tag2 =:= char           -> {I1, I2};
int_type_to_range({char, _, I})                        -> {I, I};
int_type_to_range({integer, _, I})                     -> {I, I}.

%% callback for sorting ranges.
-spec lower_bound_less_or_eq(int_range(), int_range()) -> boolean().
lower_bound_less_or_eq({A, _}, {B, _}) ->
    if
        A == neg_inf -> true;
        B == neg_inf -> false;
        true         -> A =< B
    end.

%% Converts a range back to a type. Creates two types in some cases and zero
%% types if lower bound is greater than upper bound.
-spec int_range_to_types(int_range()) -> [type()].
int_range_to_types({neg_inf, pos_inf}) ->
    [type(integer)];
int_range_to_types({neg_inf, -1}) ->
    [type(neg_integer)];
int_range_to_types({neg_inf, 0}) ->
    [type(neg_integer), {integer, erl_anno:new(0), 0}];
int_range_to_types({neg_inf, I}) when I > 0 ->
    [type(neg_integer),
     {type, erl_anno:new(0), range, [{integer, erl_anno:new(0), 0}
                                    ,{integer, erl_anno:new(0), I}]}];
int_range_to_types({neg_inf, I}) when I < -1 ->
    [{type, erl_anno:new(0), range, [{integer, erl_anno:new(0), neg_inf}
                                    ,{integer, erl_anno:new(0), I}]}];
int_range_to_types({I, pos_inf}) when I < -1 ->
    [{type, erl_anno:new(0), range, [{integer, erl_anno:new(0), I}
                                    ,{integer, erl_anno:new(0), -1}]},
     type(non_neg_integer)];
int_range_to_types({-1, pos_inf}) ->
    [{integer, erl_anno:new(0), -1}, type(non_neg_integer)];
int_range_to_types({0, pos_inf}) ->
    [type(non_neg_integer)];
int_range_to_types({1, pos_inf}) ->
    [type(pos_integer)];
int_range_to_types({I, pos_inf}) when I > 1 ->
    [{type, erl_anno:new(0), range, [{integer, erl_anno:new(0), I}
                                    ,{integer, erl_anno:new(0), pos_inf}]}];
int_range_to_types({I, I}) ->
    [{integer, erl_anno:new(0), I}];
int_range_to_types({I, J}) when is_integer(I) andalso
				is_integer(J) andalso
				I < J ->
    [{type, erl_anno:new(0), range, [{integer, erl_anno:new(0), I}
                                    ,{integer, erl_anno:new(0), J}]}];
int_range_to_types({I, J}) when I > J ->
    [].

int_max(A, B) when A == pos_inf; B == pos_inf   -> pos_inf;
int_max(neg_inf, B) -> B;
int_max(A, neg_inf) -> A;
int_max(A, B) when is_integer(A), is_integer(B) -> max(A, B).

int_min(A, B) when A == neg_inf; B == neg_inf   -> neg_inf;
int_min(pos_inf, B) -> B;
int_min(A, pos_inf) -> A;
int_min(A, B) when is_integer(A), is_integer(B) -> min(A, B).

int_negate(pos_inf) -> neg_inf;
int_negate(neg_inf) -> pos_inf;
int_negate(I) when is_integer(I) -> -I.

%% Input arg must be already normalized
negate_num_type({type, _, TyName, []} = Ty) when
      TyName =:= any;
      TyName =:= integer;
      TyName =:= float ->
    Ty;
negate_num_type({integer, P, I}) ->
    {integer, P, -I};
negate_num_type({type, P, union, Tys}) ->
    %% We normalize the result only to merge `0 | pos_integer()` =>
    %% `non_neg_integer()` and to have a nice increasing order of Tys.
    %% The incoming union type must be already normalized so it shouldn't
    %% contain any unresolved types. So it is ok to normalize the result with an
    %% empty TEnv.
    least_upper_bound:normalize({type, P, union, [negate_num_type(Ty)||Ty <- Tys]}, #tenv{});
negate_num_type(None = {type, _, none, []}) ->
    None;
negate_num_type(RangeTy) ->
    %% some kind of range type like `1..3' or `neg_integer()'
    {L, U} = type_integer:int_type_to_range(RangeTy),
    L2 = type_integer:int_negate(U),
    U2 = type_integer:int_negate(L),
    case type_integer:int_range_to_types({L2, U2}) of
        [Ty] ->
            Ty;
        Tys = [_, _] ->
            %% In some cases the result is two mutually exclusive type.
            %% (Currently only when `non_neg_integer()` => `neg_integer() | 0`)
            type(union, Tys)
    end.

-spec upper_bound_more_or_eq(int_range(), int_range()) -> boolean().
upper_bound_more_or_eq({_, A}, {_, B}) ->
    if
        A == pos_inf -> true;
        B == pos_inf -> false;
        true         -> A >= B
    end.

