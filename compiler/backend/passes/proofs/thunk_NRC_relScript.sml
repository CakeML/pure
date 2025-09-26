(*
  Theorems to help prove properties about transitive closure of relations
*)
Theory thunk_NRC_rel
Ancestors
  string option sum pair list alist finite_map pred_set rich_list
  thunkLang thunkLang_primitives wellorder arithmetic pure_misc
  thunkLangProps thunk_semantics
Libs
  term_tactic monadsyntax dep_rewrite



(* NRC lemmas *)

Theorem NRC_refl:
  ∀R x. R x x ⇒ ∀n. NRC R n x x
Proof
  gen_tac >> gen_tac >> strip_tac >>
  Induct >> gvs [Once NRC] >>
  metis_tac []
QED

Theorem NRC_INC_1:
  ∀R n m x y. R x x ∧ NRC R n x y ∧ n ≤ m ⇒ NRC R m x y
Proof
  gvs [LESS_OR_EQ] >> rw [] >> gvs [] >>
  dxrule_then assume_tac LESS_ADD >> gvs [] >>
  rename1 ‘NRC R (n + p) x y’ >>
  qspecl_then [‘y’, ‘x’, ‘n’, ‘p’, ‘R’] assume_tac $ GEN_ALL NRC_ADD_EQN >>
  gvs [] >>
  first_assum $ irule_at Any >>
  gvs [NRC_refl]
QED

Theorem NRC_INC_2:
  ∀R n m x y. R y y ∧ NRC R n x y ∧ n ≤ m ⇒ NRC R m x y
Proof
  gvs [LESS_OR_EQ] >> rw [] >> gvs [] >>
  dxrule_then assume_tac LESS_ADD >> gvs [NRC_ADD_EQN] >>
  first_assum $ irule_at Any >>
  gvs [NRC_refl]
QED

Theorem NRC_change_rel:
  (∀x y. R x y ⇒ R2 x y) ⇒
  ∀n x y. NRC R n x y ⇒ NRC R2 n x y
Proof
  strip_tac >> Induct >> gs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ irule_at Any
QED

Theorem LIST_REL_NRC_0:
  ∀xs ys. LIST_REL (NRC R 0) xs ys ⇔ xs = ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs []
QED

Theorem LIST_REL_NRC_SUC:
  ∀xs ys. LIST_REL (NRC R (SUC n)) xs ys ⇔
          ∃zs. LIST_REL R xs zs ∧ LIST_REL (NRC R n) zs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs []
  \\ rw [] \\ eq_tac \\ rw []
  \\ fs [PULL_EXISTS,NRC]
  \\ metis_tac []
QED

Theorem LIST_REL_NRC_ADD:
  ∀xs ys. LIST_REL (NRC R (m + n)) xs ys ⇔
          ∃zs. LIST_REL (NRC R m) xs zs ∧ LIST_REL (NRC R n) zs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs []
  \\ rw [] \\ eq_tac \\ rw []
  \\ fs [PULL_EXISTS,NRC_ADD_EQN]
  \\ metis_tac []
QED

Theorem LIST_REL_NRC_INC_1:
  ∀xs ys n m. LIST_REL R xs xs ∧ LIST_REL (NRC R n) xs ys ∧ n ≤ m ⇒ LIST_REL (NRC R m) xs ys
Proof
  Induct >> gvs [LIST_REL_NRC_0] >>
  gen_tac >> Cases >> rw []
  >- (irule NRC_INC_1 >> metis_tac []) >>
  last_x_assum $ dxrule_all_then irule
QED

Theorem LIST_REL_NRC_INC_2:
  ∀xs ys n m. LIST_REL R ys ys ∧ LIST_REL (NRC R n) xs ys ∧ n ≤ m ⇒ LIST_REL (NRC R m) xs ys
Proof
  Induct >> gvs [LIST_REL_NRC_0] >>
  gen_tac >> Cases >> rw []
  >- (irule NRC_INC_2 >> metis_tac []) >>
  last_x_assum $ dxrule_all_then irule
QED

Theorem NRC_rel_App:
  (∀f g x y. R f g ∧ R x y ⇒ R (App f x) (App g y)) ⇒
      ∀n f g x y. NRC R n f g ∧ NRC R n x y ⇒ NRC R n (App f x) (App g y)
Proof
  strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ irule_at Any
QED

Theorem NRC_rel_App_MAX:
  (∀f g x y. R f g ∧ R x y ⇒ R (App f x) (App g y)) ⇒
      ∀n m f g x y. NRC R n f g ∧ NRC R m x y ∧ R f f ∧ R x x ⇒ NRC R (MAX n m) (App f x) (App g y)
Proof
  rw [] >> irule NRC_rel_App >> gvs [] >>
  irule_at (Pos hd) NRC_INC_1 >>
  irule_at (Pos last) NRC_INC_1 >>
  rpt $ first_x_assum $ irule_at Any >>
  gvs [MAX_LE]
QED

Theorem NRC_rel_Apps_MAX:
  (∀f g x y. R f g ∧ R x y ⇒ R (App f x) (App g y)) ⇒
  ∀lx ly n f g. NRC R n f g ∧ LIST_REL (λx y. ∃m. NRC R m x y) lx ly ∧ R f f ∧ LIST_REL R lx lx
                ⇒ ∃n. NRC R n (Apps f lx) (Apps g ly)
Proof
  strip_tac >> Induct >> gs [PULL_EXISTS] >> rw []
  >- first_x_assum $ irule_at Any >>
  first_x_assum $ irule_at Any >> simp [] >>
  irule_at Any NRC_rel_App_MAX >> simp [] >>
  first_x_assum $ irule_at Any >>
  first_x_assum $ irule_at Any
QED

Theorem NRC_rel_If:
  (∀x1 x2 y1 y2 z1 z2. R x1 x2 ∧ R y1 y2 ∧ R z1 z2 ⇒ R (If x1 y1 z1) (If x2 y2 z2)) ⇒
  ∀n x1 y1 z1 x2 y2 z2. NRC R n x1 x2 ∧ NRC R n y1 y2 ∧ NRC R n z1 z2 ⇒ NRC R n (If x1 y1 z1) (If x2 y2 z2)
Proof
  strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ irule_at Any
QED

Theorem NRC_rel_If_MAX:
  (∀x1 x2 y1 y2 z1 z2. R x1 x2 ∧ R y1 y2 ∧ R z1 z2 ⇒ R (If x1 y1 z1) (If x2 y2 z2)) ⇒
  ∀l m n x1 y1 z1 x2 y2 z2. NRC R l x1 x2 ∧ NRC R m y1 y2 ∧ NRC R n z1 z2 ∧
                            R x1 x1 ∧ R y1 y1 ∧ R z1 z1 ⇒
                            NRC R (MAX l (MAX m n)) (If x1 y1 z1) (If x2 y2 z2)
Proof
  rw [] >> irule NRC_rel_If >> gvs [] >>
  irule_at (Pos last) NRC_INC_1 >>
  irule_at (Pos last) NRC_INC_1 >>
  irule_at (Pos last) NRC_INC_1 >>
  rpt $ first_x_assum $ irule_at Any >>
  gvs [MAX_LE]
QED

Theorem NRC_rel_Let:
  (∀opt e f x y. R e f ∧ R x y ⇒ R (Let opt e x) (Let opt f y)) ⇒
      ∀n opt e f x y. NRC R n e f ∧ NRC R n x y ⇒ NRC R n (Let opt e x) (Let opt f y)
Proof
  strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ irule_at Any
QED

Theorem NRC_rel_Let_MAX:
  (∀opt e f x y. R e f ∧ R x y ⇒ R (Let opt e x) (Let opt f y)) ⇒
      ∀n m opt e f x y. NRC R n e f ∧ NRC R m x y ∧ R e e ∧ R x x ⇒ NRC R (MAX n m) (Let opt e x) (Let opt f y)
Proof
  rw [] >> irule NRC_rel_Let >> gvs [] >>
  irule_at (Pos hd) NRC_INC_1 >>
  irule_at (Pos last) NRC_INC_1 >>
  rpt $ first_x_assum $ irule_at Any >>
  gvs [MAX_LE]
QED

Theorem NRC_rel_Var:
  ∀v. R (Var v) (Var v) ⇒
      ∀n. NRC R n (Var v) (Var v)
Proof
  gen_tac >> strip_tac >> Induct >> gvs [NRC] >>
  rpt $ last_x_assum $ irule_at Any
QED

Theorem NRC_rel_Prim:
  (∀op xs ys. LIST_REL R xs ys ⇒ R (Prim op xs) (Prim op ys))
      ⇒ ∀n op xs ys. LIST_REL (NRC R n) xs ys ⇒ NRC R n (Prim op xs) (Prim op ys)
Proof
  strip_tac >> Induct >> gvs [NRC, LIST_REL_NRC_0, LIST_REL_NRC_SUC] >>
  rw [] >>
  rpt $ last_x_assum $ drule_then $ irule_at Any
QED

Theorem NRC_rel_Monad:
  (∀mop xs ys. LIST_REL R xs ys ⇒ R (Monad mop xs) (Monad mop ys))
      ⇒ ∀n op xs ys. LIST_REL (NRC R n) xs ys ⇒ NRC R n (Monad mop xs) (Monad mop ys)
Proof
  strip_tac >> Induct >> gvs [NRC, LIST_REL_NRC_0, LIST_REL_NRC_SUC] >>
  rw [] >>
  rpt $ last_x_assum $ drule_then $ irule_at Any
QED

Theorem NRC_rel_fun:
  ∀fun. (∀x y. R x y ⇒ R (fun x) (fun y)) ⇒
      ∀n x y. NRC R n x y ⇒ NRC R n (fun x) (fun y)
Proof
  gen_tac >> strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ drule_then $ irule_at Any
QED

Theorem NRC_rel_Force:
  (∀x y. R x y ⇒ R (Force x) (Force y)) ⇒
      ∀n x y. NRC R n x y ⇒ NRC R n (Force x) (Force y)
Proof
  strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ drule_then $ irule_at Any
QED

Theorem NRC_rel_Delay:
  (∀x y. R x y ⇒ R (Delay x) (Delay y)) ⇒
      ∀n x y. NRC R n x y ⇒ NRC R n (Delay x) (Delay y)
Proof
  strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ drule_then $ irule_at Any
QED

Theorem NRC_rel_MkTick:
  (∀x y. R x y ⇒ R (MkTick x) (MkTick y)) ⇒
      ∀n x y. NRC R n x y ⇒ NRC R n (MkTick x) (MkTick y)
Proof
  strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ drule_then $ irule_at Any
QED

Theorem NRC_rel_Lam:
  (∀s x y. R x y ⇒ R (Lam s x) (Lam s y)) ⇒
      ∀n s x y. NRC R n x y ⇒ NRC R n (Lam s x) (Lam s y)
Proof
  strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  rpt $ last_x_assum $ drule_then $ irule_at Any
QED

Theorem NRC_rel_Lams_lemma:
  (∀s x y. R x y ⇒ R (Lam s x) (Lam s y)) ⇒
  (∀l x y. R x y ⇒ R (Lams l x) (Lams l y))
Proof
  strip_tac >> Induct >> gvs []
QED

Theorem NRC_rel_Lams:
  (∀s x y. R x y ⇒ R (Lam s x) (Lam s y)) ⇒
      ∀n l x y. NRC R n x y ⇒ NRC R n (Lams l x) (Lams l y)
Proof
  strip_tac >> Induct >> gvs [NRC] >>
  rw [] >>
  irule_at Any NRC_rel_Lams_lemma >> gs [] >>
  rpt $ last_x_assum $ drule_then $ irule_at Any >>
  simp []
QED

Theorem LIST_REL_NRC_MAX_1:
  ∀xs ys. LIST_REL (λx y. ∃n. NRC R n x y) xs ys ∧ LIST_REL R xs xs ⇒ ∃n. LIST_REL (NRC R n) xs ys
Proof
  Induct >> gvs [] >>
  gen_tac >> Cases >> rw [] >>
  rename1 ‘NRC R n h1 h2’ >>
  last_x_assum $ drule_all_then $ qx_choose_then ‘m’ assume_tac >>
  qexists_tac ‘MAX n m’ >>
  irule_at Any NRC_INC_1 >>
  irule_at Any LIST_REL_NRC_INC_1 >>
  rpt $ first_x_assum $ irule_at Any >>
  gvs [MAX_LE]
QED

Theorem LIST_REL_NRC_MAX_2:
  ∀xs ys. LIST_REL (λx y. ∃n. NRC R n x y) xs ys ∧ LIST_REL R ys ys ⇒ ∃n. LIST_REL (NRC R n) xs ys
Proof
  Induct >> gvs [] >>
  gen_tac >> Cases >> rw [] >>
  rename1 ‘NRC R n h1 h2’ >>
  last_x_assum $ drule_all_then $ qx_choose_then ‘m’ assume_tac >>
  qexists_tac ‘MAX n m’ >>
  irule_at Any NRC_INC_2 >>
  irule_at Any LIST_REL_NRC_INC_2 >>
  rpt $ first_x_assum $ irule_at Any >>
  gvs [MAX_LE]
QED

Definition rel_uses_Letrecs_def:
  rel_uses_Letrecs R xs x =
  ∀ys y. MAP FST xs = MAP FST ys ∧ LIST_REL R (MAP SND xs) (MAP SND ys) ∧ R x y ⇒ R (Letrec xs x) (Letrec ys y)
End

Theorem NRC_rel_Letrec:
  (∀xs ys x y. rel_uses_Letrecs R xs x ∧ R (Letrec xs x) (Letrec ys y) ⇒ rel_uses_Letrecs R ys y) ⇒
  ∀n xs ys x y. LIST_REL (NRC R n) (MAP SND xs) (MAP SND ys) ∧ MAP FST xs = MAP FST ys ∧ NRC R n x y ∧
                rel_uses_Letrecs R xs x
                ⇒ NRC R n (Letrec xs x) (Letrec ys y)
Proof
  strip_tac >> Induct >> gvs [NRC, LIST_REL_NRC_0, LIST_REL_NRC_SUC] >> rw []
  >- (irule EQ_TRANS >>
      irule_at Any $ GSYM ZIP_UNZIP >>
      once_rewrite_tac [UNZIP_MAP] >>
      gvs [] >> gvs [GSYM UNZIP_MAP]) >>
  last_x_assum $ drule_then assume_tac >>
  last_x_assum $ irule_at $ Pos last >>
  first_x_assum $ irule_at $ Pos $ el 4 >>
  first_x_assum $ irule_at $ Pos $ el 3 >>
  rename1 ‘LIST_REL R (MAP SND xs) zs’ >>
  gvs [rel_uses_Letrecs_def] >>
  first_x_assum $ irule_at Any >> gvs [SF CONJ_ss] >>
  qexists_tac ‘ZIP (MAP FST xs, zs)’ >>
  gvs [LIST_REL_EL_EQN, MAP_ZIP]
QED

Theorem NRC_rel_Letrec_MAX:
  (∀xs ys x y. rel_uses_Letrecs R xs x ∧ R (Letrec xs x) (Letrec ys y) ⇒ rel_uses_Letrecs R ys y) ⇒
  ∀n xs ys x y. LIST_REL (λx y. ∃m. NRC R m x y) (MAP SND xs) (MAP SND ys) ∧
                MAP FST xs = MAP FST ys ∧ NRC R n x y ∧
                LIST_REL R (MAP SND xs) (MAP SND xs) ∧ R x x ∧
                rel_uses_Letrecs R xs x
                ⇒ ∃n2. NRC R n2 (Letrec xs x) (Letrec ys y)
Proof
  rw [] >>
  drule_all_then (qx_choose_then ‘m’ assume_tac) LIST_REL_NRC_MAX_1 >>
  qexists_tac ‘MAX n m’ >>
  irule NRC_rel_Letrec >>
  rw [] >> gvs []
  >- last_x_assum $ dxrule_all_then irule
  >- (irule LIST_REL_NRC_INC_1 >> gvs [] >>
      first_x_assum $ irule_at Any >> gvs [])
  >- (irule NRC_INC_1 >> gvs [] >>
      first_x_assum $ irule_at Any >> gvs [])
QED

Theorem NRC_semantics:
  (∀x y. R x y ∧ closed x ⇒ semantics x Done [] = semantics y Done []) ∧
  (∀x y. R x y ∧ closed x ⇒ closed y) ⇒
  ∀n x y. NRC R n x y ∧
          closed x ⇒
          semantics x Done [] = semantics y Done []
Proof
  strip_tac >> Induct >> gvs [NRC, PULL_EXISTS] >>
  rw [] >>
  irule EQ_TRANS >>
  first_x_assum $ drule_then $ irule_at Any >>
  metis_tac []
QED

Theorem NRC_semantics_full:
  (∀x y. R x y ∧ closed x ⇒ semantics x Done [] = semantics y Done []) ∧
  (∀x y. R x y ∧ closed x ⇒ closed y) ∧
  (∀x y. R2 x y ⇒ ∃n. NRC R n x y) ⇒
  ∀x y. R2 x y ∧ closed x ⇒ semantics x Done [] = semantics y Done []
Proof
  rw [] >>
  metis_tac [NRC_semantics]
QED

Theorem NRC_semantics_safe:
  (∀x y. R x y ∧ closed x ∧ pure_semantics$safe_itree (semantics x Done [])
         ⇒ semantics x Done [] = semantics y Done []) ∧
  (∀x y. R x y ∧ closed x ⇒ closed y) ⇒
  ∀n x y. NRC R n x y ∧
          closed x ∧
          pure_semantics$safe_itree (semantics x Done []) ⇒
          semantics x Done [] = semantics y Done []
Proof
  strip_tac >> Induct >> gvs [NRC, PULL_EXISTS] >>
  rw [] >>
  irule EQ_TRANS >>
  first_x_assum $ drule_then $ irule_at Any >>
  metis_tac []
QED

Theorem NRC_semantics_safe_full:
  (∀x y. R x y ∧ closed x ∧ pure_semantics$safe_itree (semantics x Done [])
         ⇒ semantics x Done [] = semantics y Done []) ∧
  (∀x y. R x y ∧ closed x ⇒ closed y) ∧
  (∀x y. R2 x y ⇒ ∃n. NRC R n x y) ⇒
  ∀x y. R2 x y ∧ closed x ∧ pure_semantics$safe_itree (semantics x Done [])
        ⇒ semantics x Done [] = semantics y Done []
Proof
  rw [] >>
  metis_tac [NRC_semantics_safe]
QED

