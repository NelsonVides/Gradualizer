-export_type([typed_record_field/0]).

-type type() :: gradualizer_type:abstract_type().

%% Pattern macros
-define(type(T), {type, _, T, []}).
-define(type(T, A), {type, _, T, A}).

%% Data collected from epp parse tree
-record(parsedata, {
          module             :: atom(),
          export_all = false :: boolean(),
          exports    = []    :: [{atom(), integer()}],
          imports    = []    :: [{module(), atom(), integer()}],
          specs      = []    :: list(),
          types      = []    :: list(),
          opaques    = []    :: list(),
          records    = []    :: list(),
          functions  = []    :: list()
         }).

-type typed_record_field() :: {typed_record_field,
                               {record_field, erl_anno:anno(), Name :: {atom, erl_anno:anno(), atom()},
                                DefaultValue :: gradualizer_type:abstract_expr()},
                                Type :: type()}.

%% Type environment, passed around while comparing compatible subtypes
-record(tenv, {module :: module(),
               types = #{} :: #{{Name :: atom(), arity()} => {Params :: [atom()],
                                                              Body :: type()}},
               records = #{} :: #{Name :: atom()          => [typed_record_field()]}
              }).

%%% The environment passed around during typechecking.
-record(env, {fenv     = #{}
             ,imported = #{}   :: #{{atom(), arity()} => module()}
             ,venv     = #{}
             ,tenv             :: #tenv{}
             ,infer    = false :: boolean()
             ,verbose  = false :: boolean()
             ,exhaust  = true  :: boolean()
             %,tyvenv  = #{}
             }).

%% convenience guards

%% same as typechecker:is_int_type/2 but can be used as a guard
-define(is_int_type(T),
        (tuple_size(T) =:= 4 andalso
         element(1, T) =:= type andalso
         (element(3, T) =:= integer orelse
          element(3, T) =:= pos_integer orelse
          element(3, T) =:= neg_integer orelse
          element(3, T) =:= non_neg_integer orelse
          element(3, T) =:= range))
        orelse
          (tuple_size(T) =:= 3 andalso
           (element(1, T) =:= integer orelse
            element(1, T) =:= char))).

%% same as typechecker:is_list_type/1 but can be used as a guard
-define(is_list_type(T),
        (tuple_size(T) =:= 4 andalso
         element(1, T) =:= type andalso
         (element(3, T) =:= list orelse
          element(3, T) =:= nil orelse
          element(3, T) =:= nonempty_list orelse
          element(3, T) =:= maybe_improper_list orelse
          element(3, T) =:= nonempty_improper_list))).
