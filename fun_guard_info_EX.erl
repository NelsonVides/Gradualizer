-module(fun_guard_info).
-compile([export_all, debug_info]).

-gradualizer(infer).

%% no spec
my_sleep(N) when is_integer(N), N > 0 -> timer:sleep(N);
my_sleep(true) -> timer:sleep(1000);
my_sleep(false) -> ok.

% -spec guard_is_atom(atom() | list()) -> list().
% guard_is_atom(Name) when Name =:= name ->
%     erlang:atom_to_list(Name).
