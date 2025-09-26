(*
  Composition of compiler passes from pureLang to CakeML, not including
  pureLang-to-pureLang passes.
 *)
Theory pure_to_cake
Ancestors
  pure_comp_conf
  pure_to_thunk thunk_to_env env_to_state state_to_cake
Libs
  term_tactic monadsyntax dep_rewrite


Definition pure_to_env_def:
  pure_to_env (c:compiler_opts) e =
    let thunk_prog = pure_to_thunk$compile_to_thunk c e in
    let _ = empty_ffi (strlit "to_thunk") in
    let env_prog = thunk_to_env$to_env thunk_prog in
    let _ = empty_ffi (strlit "to_env") in
      env_prog
End

Definition pure_to_state_def:
  pure_to_state c e =
    let env_prog = pure_to_env c e in
    let state_prog = compile_to_state c env_prog in
    let _ = empty_ffi (strlit "to_state") in
      state_prog
End

Definition pure_to_cake_def:
  pure_to_cake c ns e =
    let state_prog = pure_to_state c e in
    let cake_prog = compile_with_preamble c ((I ## K ns) initial_namespace) state_prog in
    let _ = empty_ffi (strlit "to_cake") in
      cake_prog
End
