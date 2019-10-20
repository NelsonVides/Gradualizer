-module(type_inference).
-include("typelib.hrl").

-export([
         infer_literal_type/1
        ]).

-import(typelib, [type/2, type/1, return/1]).

infer_literal_type({string, _, Chars}) ->
    ActualyTy = infer_literal_string(Chars),
    return(ActualyTy);
infer_literal_type({nil, _}) ->
    return(type(nil));
infer_literal_type({atom, _, _} = Atom) ->
    return(Atom);
infer_literal_type({integer, _, _N} = Integer) ->
    return(Integer);
infer_literal_type({float, _, _F}) ->
    return(type(float));
infer_literal_type({char, _, _C} = Char) ->
    return(Char).

infer_literal_string("") ->
    type(nil);
infer_literal_string(Str) ->
    SortedChars = lists:usort(Str),
    if length(SortedChars) =< 10 ->
            %% heuristics: if there are not more than 10 different characters
            %% list them explicitely as singleton types
            CharTypes = [{char, erl_anno:new(0), C} || C <- SortedChars],
            type(nonempty_list, [least_upper_bound:normalize(type(union, CharTypes), #tenv{})]);
       true ->
            type(nonempty_list,
                 [type(range, [{char, erl_anno:new(0), hd(SortedChars)},
                               {char, erl_anno:new(0), lists:last(SortedChars)}])])
    end.
