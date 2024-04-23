(*
  Inlining optimization proofs for cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open pred_setTheory listTheory;
open pure_inline_rel_altTheory pure_inline_cexpTheory pure_presTheory
     pure_dead_letProofTheory pure_freshenProofTheory;

val _ = new_theory "pure_inlineProof";

(* xs and m have the same elements *)
Definition memory_inv_def:
  memory_inv xs m (ns:(mlstring,unit) map # num) ⇔
    { a | ∃e. lookup m a = SOME e } = BIGUNION (set $ MAP lhs_names xs) ∧
    EVERY (λx. case x of
      | pure_inline_rel_alt$Simple d v r =>
          explode v ∈ set_of ns ∧ avoid_set_ok ns r
      | Rec d rs =>
          EVERY (λ(v,r). explode v ∈ set_of ns ∧ avoid_set_ok ns r) rs) xs ∧
    (∀v e. lookup m v = SOME $ pure_inline_cexp$Simple e ⇒
      ∃d. MEM (pure_inline_rel_alt$Simple d v e) xs ∧
          avoid_set_ok ns e ∧
          NestedCase_free e ∧ letrecs_distinct (exp_of e) ∧ cexp_wf e) ∧
    (∀v e. lookup m v = SOME $ pure_inline_cexp$Rec e ⇒
      ∃fns d. MEM (pure_inline_rel_alt$Rec d fns) xs ∧ MEM (v,e) fns ∧
            avoid_set_ok ns e ∧ NestedCase_free e ∧ letrecs_distinct (exp_of e) ∧ cexp_wf e)
End

Definition LIST_REL3_def:
  LIST_REL3 R [] [] [] = T ∧
  LIST_REL3 R (x::xs) (y::ys) (z::zs) = (R x y z ∧ LIST_REL3 R xs ys zs) ∧
  LIST_REL3 _ _ _ _ = F
End

fun lemma () = inline_ind
  |> Q.SPEC ‘λm ns cl h x. ∀xs t ns1.
    memory_inv xs m ns ∧
    map_ok m ∧
    avoid_set_ok ns x ∧
    NestedCase_free x ∧
    letrecs_distinct (exp_of x) ∧
    cexp_wf x ∧
    barendregt (exp_of x) ∧
    DISJOINT (BIGUNION (set $ MAP lhs_names xs))
             (IMAGE implode $ boundvars (exp_of x)) ∧
    (inline m ns cl h x) = (t, ns1) ⇒
    inline_rel xs x t’
  |> Q.SPEC ‘λm ns cl h es. ∀xs ts ns1.
    memory_inv xs m ns ∧
    map_ok m ∧
    EVERY (λx.
             avoid_set_ok ns x ∧
             NestedCase_free x ∧
             letrecs_distinct (exp_of x) ∧
             cexp_wf x) es ∧
    EVERY (λe. barendregt (exp_of e)) es ∧
    EVERY (λx. DISJOINT (BIGUNION (set $ MAP lhs_names xs))
                        (IMAGE implode $ boundvars (exp_of x))) es ∧
    (inline_list m ns cl h es) = (ts, ns1) ⇒
    LIST_REL (λx t. inline_rel xs x t) es ts’
  |> Q.SPEC ‘λms ns cl ctxs es. T`
  |> CONV_RULE (DEPTH_CONV BETA_CONV);

Theorem inline_cexp_inline_rel:
  ^(lemma() |> concl |> rand)
Proof
  cheat
QED

Theorem inline_cexp_inline_rel_spec:
  ∀m ns cl h x xs t ns1.
    memory_inv xs m ns ∧
    map_ok m ∧ avoid_set_ok ns x ∧
    NestedCase_free x ∧ cexp_wf x ∧ letrecs_distinct (exp_of x) ∧
    barendregt (exp_of x) ∧
    DISJOINT (BIGUNION $ set (MAP lhs_names xs))
             (IMAGE implode $ boundvars (exp_of x)) ∧
    (inline m ns cl h x) = (t, ns1) ⇒
    inline_rel xs x t
Proof
  rw[] >>
  drule $ cj 1 inline_cexp_inline_rel >> rpt $ disch_then drule >>
  disch_then irule >> rw[] >> goal_assum drule
QED

Theorem inline_all_thm:
  ∀cl h x.
    NestedCase_free x ∧
    letrecs_distinct (exp_of x) ∧
    cexp_wf x ∧
    closed (exp_of x) ⇒
    (exp_of x) ≅ (exp_of (inline_all cl h x))
Proof
  rw []
  \\ fs [inline_all_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ irule pure_congruenceTheory.exp_eq_trans
  \\ irule_at (Pos last) (CONJUNCT1 $ SPEC_ALL pure_dead_letProofTheory.dead_let_correct)
  \\ irule pure_congruenceTheory.exp_eq_trans
  \\ irule_at (Pos last) pres_imp_exp_eq
  \\ irule_at Any inline_rel_theorem
  \\ irule_at Any inline_cexp_inline_rel_spec \\ fs []
  \\ pop_assum $ irule_at Any \\ fs []
  \\ fs [memory_inv_def]
  \\ drule freshen_cexp_correctness
  \\ impl_tac
  >- fs [avoid_set_ok_boundvars_of]
  \\ strip_tac
  \\ fs [pure_expTheory.closed_def]
  \\ drule_at Any freshen_cexp_letrecs_distinct
  \\ simp[boundvars_of_SUBSET]
QED

(********** Syntactic well-formedness results **********)

Theorem inline_all_wf:
  inline_all cl h ce = ce' ∧ closed (exp_of ce) ∧
  NestedCase_free ce ∧ cexp_wf ce ∧ letrecs_distinct (exp_of ce)
  ⇒ closed (exp_of ce') ∧
    NestedCase_free ce' ∧ cexp_wf ce' ∧ letrecs_distinct (exp_of ce') ∧
    cns_arities ce' ⊆ cns_arities ce
Proof
  simp[inline_all_def] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  drule freshen_cexp_correctness >> rpt $ disch_then $ drule_at Any >>
  simp[avoid_set_ok_boundvars_of] >> strip_tac >>
  dxrule_at (Pos last) inline_cexp_inline_rel_spec >>
  disch_then $ qspec_then `[]` mp_tac >> impl_keep_tac >> fs[memory_inv_def]
  >- (
    gvs[avoid_set_ok_def] >> irule unique_boundvars_letrecs_distinct >>
    gvs[pure_barendregtTheory.barendregt_def]
    ) >>
  strip_tac >> drule inline_rel_theorem >> simp[] >>
  gvs[pure_expTheory.closed_def] >> strip_tac >>
  drule pres_imp_wf_preserved >> simp[] >> strip_tac >>
  drule pres_imp_freevars_preserved >> strip_tac >>
  drule pres_imp_cns_arities_preserved >> strip_tac >>
  qspec_then `inlined_e` assume_tac dead_let_correct >> gvs[] >>
  gvs[pure_expTheory.closed_def, SUBSET_DEF]
QED

(********** Top-level theorems **********)

Theorem inline_top_level_correct:
  NestedCase_free ce ∧
  letrecs_distinct (exp_of ce) ∧
  cexp_wf ce ∧
  closed (exp_of ce) ∧
  inline_top_level c ce = ce'
  ⇒ exp_of ce ≅ exp_of ce' ∧
    NestedCase_free ce' ∧
    letrecs_distinct (exp_of ce') ∧
    cexp_wf ce' ∧
    closed (exp_of ce') ∧
    (cns_arities ce' ⊆ cns_arities ce)
Proof
  simp[inline_top_level_def] >> strip_tac >> gvs[] >>
  drule_all inline_all_thm >> dxrule_at Any inline_all_wf >>
  rpt $ disch_then $ dxrule_at Any >> strip_tac >> gvs[]
QED

(*******************)

val _ = export_theory();
