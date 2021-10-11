(*
   Observable semantics for thunkLang.
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_semanticsTheory pure_configTheory
     thunkLang_primitivesTheory thunkLangTheory io_treeTheory;

val _ = new_theory "thunk_semantics";

val _ = set_grammar_ancestry ["thunkLang", "io_tree"];

(******************** Datatypes and helpers ********************)

Datatype:
  cont = Done      (* nothing left to do *)
       | BC v cont (* RHS of Bind, rest *)
       | HC v cont (* RHS of Handle, rest *)
End

Type state[pp] = “:(v list) list”;

Datatype:
  next_res = Act 'e cont state | Ret | Div | Err
End

Definition force_def:
  force v =
    do
      (wx, binds) <- dest_anyThunk v;
      case wx of
        INL v => return v
      | INR y => eval (subst_funs binds y)
    od
End

Definition force_list_def:
  force_list [] = INR [] ∧
  force_list (v::vs) =
    case (force v, force_list vs) of
    | (INL err, _)    => INL err
    | (_, INL err)    => INL err
    | (INR w, INR ws) => INR (w::ws)
End

Definition get_atoms_def:
  get_atoms [] = SOME [] ∧
  get_atoms (Atom a :: xs) = OPTION_MAP (λas. a::as) (get_atoms xs) ∧
  get_atoms _ = NONE
End

Definition with_atoms_def:
  with_atoms vs f =
    case force_list vs of
    | INL Diverge => Div
    | INL Type_error => Err
    | INR ws =>
      case get_atoms vs of
      | SOME as => f as
      | NONE => Err
End

Definition apply_closure_def:
  apply_closure f arg cont =
    case dest_anyClosure f of
    | INR (x, body, binds) => cont (eval (subst (binds ++ [(x,arg)]) body))
    | _ => Err
End

Definition force_apply_closure_def:
  force_apply_closure f arg cont =
    case force f of
    | INR f' => apply_closure f' arg cont
    | INL Diverge => Div
    | INL Type_error => Err
End

(******************** Intermediate definitions ********************)

Definition next_def:
  next (k:num) sv stack (state:state) =
    case sv of
    | INL Diverge => Div
    | INL _ => Err
    | INR v =>
      case v of
      | Constructor s vs => (
          if s = "Ret" ∧ LENGTH vs = 1 then
            (case stack of
             | Done => Ret
             | BC f fs =>
                force_apply_closure f (HD vs)
                  (λw. if k = 0 then Div else next (k-1) w fs state)
             | HC f fs => if k = 0 then Div else next (k-1) sv fs state)
          else if s = "Raise" ∧ LENGTH vs = 1 then
            (case stack of
             | Done => Ret
             | BC f fs => if k = 0 then Div else next (k-1) sv fs state
             | HC f fs =>
                force_apply_closure f (HD vs)
                  (λw. if k = 0 then Div else next (k-1) w fs state))
          else if s = "Bind" ∧ LENGTH vs = 2 then
            (let m = EL 0 vs in
             let f = EL 1 vs in
               if k = 0 then Div else next (k-1) (INR m) (BC f stack) state)
          else if s = "Handle" ∧ LENGTH vs = 2 then
            (let m = EL 0 vs in
             let f = EL 1 vs in
               if k = 0 then Div else next (k-1) (INR m) (HC f stack) state)
          else if s = "Act" ∧ LENGTH vs = 1 then
            (with_atoms vs (λas.
               case HD as of
               | Msg channel content => Act (channel, content) stack state
               | _ => Err))
          else if s = "Alloc" ∧ LENGTH vs = 2 then
            (with_atoms [HD vs] (λas.
               case HD as of
               | Int len =>
                   (let n = if len < 0 then 0 else Num len in
                    let new_state = state ++ [REPLICATE n (EL 1 vs)] in
                      if k = 0 then Div else
                        next (k-1)
                          (INR $ Constructor "Ret" [Atom (Loc (LENGTH state))])
                          stack new_state)
               | _ => Err))
          else if s = "Length" ∧ LENGTH vs = 1 then
            (with_atoms vs (λas.
               case HD as of
               | Loc n =>
                   (if LENGTH state ≤ n then Err else
                    if k = 0 then Div else
                      next (k-1)
                        (INR $ Constructor "Ret" [Atom (Int (& (LENGTH (EL n state))))])
                        stack state)
               | _ => Err))
          else if s = "Deref" ∧ LENGTH vs = 2 then
            (with_atoms vs (λas.
               case (EL 0 as, EL 1 as) of
               | (Loc n, Int i) =>
                   (if LENGTH state ≤ n then Err else
                    if k = 0 then Div else
                    if 0 ≤ i ∧ i < & LENGTH (EL n state) then
                      next (k-1)
                        (INR $ Constructor "Ret" [EL (Num i) (EL n state)])
                        stack state
                    else
                      next (k-1)
                        (INR $ Constructor "Raise" [Constructor "Subscript" []])
                        stack state)
               | _ => Err))
          else if s = "Update" ∧ LENGTH vs = 3 then
            (with_atoms [EL 0 vs; EL 1 vs] (λas.
               case (EL 0 as, EL 1 as) of
               | (Loc n, Int i) =>
                   (if LENGTH state ≤ n then Err else
                    if k = 0 then Div else
                    if 0 ≤ i ∧ i < & LENGTH (EL n state) then
                      next (k-1)
                        (INR $ Constructor "Ret" [Constructor "" []])
                        stack
                        (LUPDATE (LUPDATE (EL 2 vs) (Num i) (EL n state)) n state)
                    else
                      next (k-1)
                        (INR $ Constructor "Raise" [Constructor "Subscript" []])
                        stack state)
               | _ => Err))
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
    io_unfold_err
      (λ(sv,stack,state).
        case next_action sv stack state of
        | Ret => Ret' pure_semantics$Termination
        | Err => Ret' pure_semantics$Error
        | Div => Div'
        | Act a new_stack new_state =>
            Vis' a
              (λy. (INR $ Constructor "Ret" [Atom (Str y)], new_stack, new_state)))
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
                interp (INR $ Constructor "Ret" [Atom (Str y)]) new_stack new_state
              else Ret $ pure_semantics$FinalFFI a pure_semantics$FFI_failure)
Proof
  rw[Once interp, interp'_def] >>
  once_rewrite_tac[io_unfold_err] >> gvs[] >>
  CASE_TAC >> gvs[combinTheory.o_DEF, FUN_EQ_THM] >> rw[] >>
  CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >>
  rw[Once interp, interp'_def]
QED

Definition semantics_def:
  semantics e stack state = interp (eval e) stack state
End

Definition itree_of_def:
  itree_of e = semantics e Done []
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
  Cases_on `s = "Bind"` >- (gvs[] >> rw[]) >>
  Cases_on `s = "Handle"` >- (gvs[] >> rw[]) >>
  Cases_on `s = "Act"` >- (gvs[] >> rw[]) >>
  Cases_on `s = "Raise"` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >- (IF_CASES_TAC >> gvs[]) >>
    simp[apply_closure_def,force_apply_closure_def] >> rpt $ TOP_CASE_TAC >> gvs[]
    ) >>
  Cases_on `s = "Ret"` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >>
    reverse $ TOP_CASE_TAC >> gvs[] >- (IF_CASES_TAC >> gvs[]) >>
    simp[apply_closure_def,force_apply_closure_def] >> rpt $ TOP_CASE_TAC >> gvs[]
    ) >>
  Cases_on `s = "Alloc"` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> rw[with_atoms_def,force_list_def] >>
    ntac 4 (TOP_CASE_TAC >> gvs[]) >>
    first_x_assum irule >> simp[] >> qexists_tac `[Int i]` >> simp[]
    ) >>
  Cases_on `s = "Length"` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> rw[with_atoms_def,force_list_def] >>
    ntac 5 (TOP_CASE_TAC >> gvs[]) >>
    first_x_assum irule >> simp[] >> qexists_tac `[Loc n]` >> simp[]
    ) >>
  Cases_on `s = "Deref"` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> rw[with_atoms_def,force_list_def] >>
    ntac 7 (TOP_CASE_TAC >> gvs[]) >>
    first_x_assum irule >> simp[] >> qexists_tac `[Loc n; Int i]` >> simp[]
    ) >>
  Cases_on `s = "Update"` >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >> rw[with_atoms_def,force_list_def] >>
    ntac 7 (TOP_CASE_TAC >> gvs[]) >>
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

val _ = export_theory();
