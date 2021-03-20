
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     pairTheory pred_setTheory;
open pure_expTheory pure_exp_lemmasTheory
     pure_exp_relTheory pure_congruenceTheory

val _ = new_theory "pure_ctxt_equiv";


(******************** Basic definitions ********************)

Datatype:
  ctxt = Hole
       | Prim op (exp list) ctxt (exp list)
       | AppL ctxt exp
       | AppR exp ctxt
       | Lam vname ctxt
       | LetrecL ((vname # exp) list)
                  (vname # ctxt)
                 ((vname # exp) list) exp
       | LetrecR ((vname # exp) list) ctxt
End

Definition plug_def:
  plug Hole n = n ∧
  plug (Prim op xs1 h xs2) n = Prim op (xs1 ++ [plug h n] ++ xs2) ∧
  plug (AppL h y) n = App (plug h n) y ∧
  plug (AppR x h) n = App x (plug h n) ∧
  plug (Lam v h) n = Lam v (plug h n) ∧
  plug (LetrecL xs1 (f,h) xs2 x) n = Letrec (xs1 ++ [(f,plug h n)] ++ xs2) x ∧
  plug (LetrecR xs h) n = Letrec xs (plug h n)
End

Definition plug_ctxt_def:
  plug_ctxt Hole n = n ∧
  plug_ctxt (Prim op xs1 h xs2) n = Prim op xs1 (plug_ctxt h n) xs2 ∧
  plug_ctxt (AppL h y) n = AppL (plug_ctxt h n) y ∧
  plug_ctxt (AppR x h) n = AppR x (plug_ctxt h n) ∧
  plug_ctxt (Lam v h) n = Lam v (plug_ctxt h n) ∧
  plug_ctxt (LetrecL xs1 (f,h) xs2 x) n = LetrecL xs1 (f, plug_ctxt h n) xs2 x ∧
  plug_ctxt (LetrecR xs h) n = LetrecR xs (plug_ctxt h n)
End

Definition AppLs_def:
  AppLs c [] = c ∧
  AppLs c (e::es) = AppLs (AppL c e) es
End

Definition LamsC_def:
  LamsC [] c = c :ctxt ∧
  LamsC (v::vs) c = Lam v (LamsC vs c)
End


(******************** Lemmas ********************)

Theorem plug_AppLs:
  ∀l c e. plug (AppLs c l) e = Apps (plug c e) l
Proof
  Induct >> rw[AppLs_def, Apps_def, plug_def]
QED

Theorem plug_LamsC:
  ∀l c e. plug (LamsC l c) e = Lams l (plug c e)
Proof
  Induct >> rw[LamsC_def, Lams_def, plug_def]
QED

Theorem plug_plug_ctxt:
  ∀c1 c2 e. plug (plug_ctxt c1 c2) e = plug c1 (plug c2 e)
Proof
  recInduct plug_ctxt_ind >> rw[plug_def, plug_ctxt_def]
QED

Theorem exp_equiv_plug:
  ∀h x y. x ≅ y ⇒ plug h x ≅ plug h y
Proof
  recInduct plug_ind >> rw[plug_def]
  >- ( (* Prim *)
    irule exp_eq_Prim_cong >>
    irule LIST_REL_APPEND_suff >> simp[] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
  >- ( (* AppL *)
    irule exp_eq_App_cong >> simp[exp_eq_refl]
    )
  >- ( (* AppR *)
    irule exp_eq_App_cong >> simp[exp_eq_refl]
    )
  >- ( (* Lam *)
    irule exp_eq_Lam_cong >> simp[exp_eq_refl]
    )
  >- ( (* LetrecL *)
    irule exp_eq_Letrec_cong >> simp[exp_eq_refl] >>
    irule LIST_REL_APPEND_suff >> simp[] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
  >- ( (* LetrecR *)
    irule exp_eq_Letrec_cong >> simp[exp_eq_refl] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
QED

Theorem freevars_plug_eq:
  ∀ctxt e1 e2.
    freevars e1 = freevars e2
  ⇒ freevars (plug ctxt e1) = freevars (plug ctxt e2)
Proof
  recInduct plug_ind >> rw[plug_def]
  >- (AP_THM_TAC >> ntac 2 AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (AP_THM_TAC >> AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (AP_THM_TAC >> AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (
    AP_THM_TAC >> ntac 2 AP_TERM_TAC >> AP_THM_TAC >>
    ntac 2 AP_TERM_TAC >> first_x_assum irule >> simp[]
    )
  >- (
    AP_THM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
    first_x_assum irule >> simp[]
    )
QED

Triviality app_bisimilarity_plug:
  ∀c x y. x ≃ y ∧ closed (plug c x) ⇒ plug c x ≃ plug c y
Proof
  rw[app_bisimilarity_eq]
  >- (irule exp_equiv_plug >> simp[])
  >- (
    gvs[closed_def] >>
    qspecl_then [`c`,`x`,`y`] assume_tac freevars_plug_eq >> gvs[]
    )
QED


(****************************************)

val _ = export_theory();
