-module(fun_guard_info_infer).
-export([
         fun_correct_arity/1,
         fun_unspecified_arity/1,
         fun_different_variables/2
         % my_sleep/1
        ]).

-gradualizer(infer).

-spec fun_correct_arity(any()) -> boolean().
fun_correct_arity(Fun) when is_function(Fun, 2) ->
    Fun(0, 1);
fun_correct_arity(_Fun) -> true.

-spec fun_unspecified_arity(any()) -> boolean().
fun_unspecified_arity(Fun) when is_function(Fun) ->
    Fun(0,1);
fun_unspecified_arity(_Fun) -> true.

-spec fun_different_variables(any(), any()) -> any().
fun_different_variables(A,B)
  when is_atom(A), is_integer(B);
       is_integer(A), is_atom(B) ->
    ok.

%% no spec
% my_sleep(N) when is_integer(N), N > 0 -> timer:sleep(N);
% my_sleep(true) -> timer:sleep(1000);
% my_sleep(false) -> ok.
