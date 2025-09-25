(*
   Observable semantics for envLang.
*)
Theory env_semantics
Ancestors
  string option sum pair list alist pure_semantics
  pure_config thunkLang_primitives
  envLang itree
Libs
  BasicProvers

(******************** Datatypes and helpers ********************)

Datatype:
  cont = Done                (* nothing left to do *)
       | BC (env # exp) cont (* RHS of Bind, rest *)
       | HC (env # exp) cont (* RHS of Handle, rest *)
End

Type state[pp] = “:(v list) list”;

Datatype:
  next_res = Act 'e cont state | Ret | Div | Err
End

Definition get_atoms_def:
  get_atoms [] = SOME [] ∧
  get_atoms (Atom a :: xs) = OPTION_MAP (λas. a::as) (get_atoms xs) ∧
  get_atoms _ = NONE
End

Definition with_atoms_def:
  with_atoms env vs f =
    case result_map (eval env) vs of
    | INL Diverge => Div
    | INL Type_error => Err
    | INR ws =>
      case get_atoms ws of
      | SOME as => f as
      | NONE => Err
End

Definition with_value_def:
  with_value e f =
    case UNCURRY eval e of
    | INR v => f v
    | INL Diverge => Div
    | INL _ => Err
End

Definition apply_closure_def:
  apply_closure f arg cont =
    with_value f (λv.
      case dest_anyClosure v of
      | INR (x, env, body) =>
          cont (eval ((x, arg)::env) body)
      | INL _ => Err)
End



(******************** Intermediate definitions ********************)

Overload Lit = “λl. Prim (AtomOp (Lit l)) []”;
Overload RetExp = “λe. Monadic [] Ret [e]”;
Overload RetVal = “λv. Monadic ["v", v] Ret [Var "v"]”
Overload RaiseExp = “λe. Monadic [] Raise [e]”;

Definition next_def:
  next (k:num) sv stack (state:state) =
    case sv of
    | INL Diverge => Div
    | INL _ => Err
    | INR v =>
      case v of
      | Monadic env mop vs => (
          if mop = Ret ∧ LENGTH vs = 1 then
            with_value (env, HD vs) (λv.
              case stack of
              | Done => Ret
              | BC f fs =>
                  if k = 0 then Div else
                    apply_closure f v (λw. next (k-1) w fs state)
              | HC f fs => if k = 0 then Div else next (k-1) sv fs state)
          else if mop = Raise ∧ LENGTH vs = 1 then
            with_value (env, HD vs) (λv.
              case stack of
              | Done => Ret
              | BC f fs => if k = 0 then Div else next (k-1) sv fs state
              | HC f fs =>
                  if k = 0 then Div else
                    apply_closure f v (λw. next (k-1) w fs state))
          else if mop = Bind ∧ LENGTH vs = 2 then
            (let m = EL 0 vs in
             let f = EL 1 vs in
               if k = 0 then Div
               else next (k-1) (eval env m) (BC (env,f) stack) state)
          else if mop = Handle ∧ LENGTH vs = 2 then
            (let m = EL 0 vs in
             let f = EL 1 vs in
               if k = 0 then Div
               else next (k-1) (eval env m) (HC (env,f) stack) state)
          else if mop = Act ∧ LENGTH vs = 1 then
            (with_atoms env vs (λas.
               case HD as of
               | Msg channel content => Act (channel, content) stack state
               | _ => Err))
          else if mop = Alloc ∧ LENGTH vs = 2 then
            (case result_map (eval env) vs of
             | INR [vl; v] =>
                (case get_atoms [vl] of
                 | SOME [Int len] =>
                    let n = if len < 0 then 0 else Num len in
                    let new_state = state ++ [REPLICATE n v] in
                    if k = 0 then Div else
                      next (k-1)
                        (INR $ RetExp $ Lit $ Loc (LENGTH state))
                        stack new_state
                 | _ => Err)
             | INL Diverge => Div
             | _ => Err)
          else if mop = Length ∧ LENGTH vs = 1 then
            (with_atoms env vs (λas.
               case HD as of
               | Loc n =>
                   (if LENGTH state ≤ n then Err else
                    if k = 0 then Div else
                      next (k-1)
                        (INR $ RetExp $ Lit $ Int (& (LENGTH (EL n state))))
                        stack state)
               | _ => Err))
          else if mop = Deref ∧ LENGTH vs = 2 then
            (with_atoms env vs (λas.
               case (EL 0 as, EL 1 as) of
               | (Loc n, Int i) =>
                   (if LENGTH state ≤ n then Err else
                    if k = 0 then Div else
                    if 0 ≤ i ∧ i < & LENGTH (EL n state) then
                      next (k-1)
                        (INR $ RetVal $ EL (Num i) (EL n state))
                        stack state
                    else
                      next (k-1)
                        (INR $ RaiseExp $ Prim (Cons "Subscript") [])
                        stack state)
               | _ => Err))
          else if mop = Update ∧ LENGTH vs = 3 then
            (case result_map (eval env) vs of
             | INR [vl; vi; v] =>
                 (case get_atoms [vl; vi] of
                  | SOME [Loc n; Int i] =>
                      if LENGTH state ≤ n then Err else
                      if k = 0 then Div else
                      if 0 ≤ i ∧ i < & LENGTH (EL n state) then
                        let new_state =
                          LUPDATE (LUPDATE v (Num i) (EL n state)) n state
                        in next (k-1)
                            (INR $ RetExp $ Prim (Cons "") [])
                            stack new_state
                      else
                        next (k-1)
                          (INR $ RaiseExp $ Prim (Cons "Subscript") [])
                          stack state
                  | _ => Err)
             | INL Diverge => Div
             | _ => Err)
          else Err)
      | _ => Err
End

Definition next_action_def:
  next_action sv stack state =
    case some k. next k sv stack state ≠ Div of
    | NONE => Div
    | SOME k => next k sv stack state
End

Definition interp'_def:
  interp' =
    itree_unfold_err
      (λ(sv,stack,state).
        case next_action sv stack state of
        | Ret => Ret' pure_semantics$Termination
        | Err => Ret' pure_semantics$Error
        | Div => Div'
        | Act a new_stack new_state =>
            Vis' a
              (λy. (INR $ Monadic [("v", Atom $ Str y)] Ret [Var "v"],
                    new_stack, new_state)))
      ((λ_ ret. STRLEN ret ≤ max_FFI_return_size),
       pure_semantics$FinalFFI,
       λs. pure_semantics$FinalFFI s pure_semantics$FFI_failure)
End

(******************** Top-level definitions ********************)

Definition interp:
  interp sv stack state = interp' (sv, stack, state)
End

Theorem interp_def:
  interp sv stack state =
    case next_action sv stack state of
    | Ret => Ret pure_semantics$Termination
    | Div => Div
    | Err => Ret pure_semantics$Error
    | Act a new_stack new_state =>
        Vis a (λs. case s of
          | INL x =>
              Ret $ pure_semantics$FinalFFI a x
          | INR y =>
              if STRLEN y ≤ max_FFI_return_size then
                interp (INR $ Monadic [("v",Atom $ Str y)] Ret [Var "v"])
                  new_stack new_state
              else Ret $ pure_semantics$FinalFFI a pure_semantics$FFI_failure)
Proof
  rw[Once interp, interp'_def] >>
  once_rewrite_tac[itree_unfold_err] >> gvs[] >>
  CASE_TAC >> gvs[combinTheory.o_DEF, FUN_EQ_THM] >> rw[] >>
  CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >>
  rw[Once interp, interp'_def]
QED

Definition semantics_def:
  semantics e env stack state = interp (eval env e) stack state
End

Definition itree_of_def:
  itree_of e = semantics e [] Done []
End


(******************** Lemmas ********************)

Theorem next_less_eq:
  ∀n e k st m.
    next n e k st ≠ Div ∧
    n ≤ m
  ⇒ next n e k st = next m e k st
Proof
  recInduct next_ind >> rw[] >>
  ntac 2 $ pop_assum mp_tac >>
  once_rewrite_tac[next_def] >>
  TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
  rename1 `s = Ret` >>
  Cases_on `s = Bind` >- (gvs[] >> rw[]) >>
  Cases_on `s = Handle` >- (gvs[] >> rw[]) >>
  Cases_on `s = Act` >- (gvs[] >> rw[]) >>
  Cases_on `s = Raise` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> simp[with_value_def] >>
    ntac 2 (TOP_CASE_TAC >> gvs[]) >- (IF_CASES_TAC >> gvs[]) >>
    simp[apply_closure_def, with_value_def] >> rpt $ TOP_CASE_TAC >> gvs[]
    ) >>
  Cases_on `s = Ret` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> simp[with_value_def] >>
    ntac 2 (reverse TOP_CASE_TAC >> gvs[]) >- (IF_CASES_TAC >> gvs[]) >>
    simp[apply_closure_def, with_value_def] >> rpt $ TOP_CASE_TAC >> gvs[]
    ) >>
  Cases_on `s = Alloc` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> rw[with_atoms_def, with_value_def] >>
    rpt (TOP_CASE_TAC >> gvs[]) >> first_x_assum drule >> simp[]
    ) >>
  Cases_on `s = Length` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> rw[with_atoms_def] >>
    ntac 5 (TOP_CASE_TAC >> gvs[]) >>
    first_x_assum irule >> simp[] >> qexists_tac `[Loc n]` >> simp[]
    ) >>
  Cases_on `s = Deref` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> rw[with_atoms_def] >>
    ntac 7 (TOP_CASE_TAC >> gvs[]) >>
    first_x_assum irule >> simp[] >> qexists_tac `[Loc n; Int i]` >> simp[]
    ) >>
  Cases_on `s = Update` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> rw[with_atoms_def, with_value_def] >>
    rpt (TOP_CASE_TAC >> gvs[]) >>
    first_x_assum irule >> simp[] >> qexists_tac `[Loc n; Int i]` >> simp[]
    )
QED

Theorem next_next:
  next n e k st ≠ Div ∧ next m e k st ≠ Div ⇒
  next n e k st = next m e k st
Proof
  metis_tac [arithmeticTheory.LESS_EQ_CASES, next_less_eq]
QED

(****************************************)
