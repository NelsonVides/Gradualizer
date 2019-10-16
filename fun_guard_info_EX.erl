-module(fun_guard_info).
-compile([export_all, debug_info]).

-spec guard_is_atom(atom() | list()) -> list().
guard_is_atom(Name) when Name =:= name ->
    erlang:atom_to_list(Name).

-spec fun_different_variables(any(), any()) -> any().
fun_different_variables(A,B)
  when is_atom(A), is_integer(B);
       is_integer(A), is_atom(B) ->
    case is_atom(A) of
        true -> erlang:atom_to_list(A) + B;
        _ -> ok
    end;
fun_different_variables(A,B) ->
    A ++ B.
