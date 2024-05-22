(* testing the typing rules for typeclassLang *)
(* the example program in Haskell is in
 * test_typeclass_typing.hs and the translated version is
 * in test_typeclass_typing_translated.hs *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory miscTheory;
open listTheory alistTheory relationTheory set_relationTheory pred_setTheory;
open pure_cexpTheory pure_configTheory;
open typeclass_typesTheory typeclass_typesPropsTheory;
open typeclass_texpTheory typeclass_kindCheckTheory;
open typeclass_typingTheory;

val _ = new_theory "test_typeclass_typing";

(* Monoid [mappend;mempty], Foldable [foldMap] *)
Definition test_class_env_def:
  test_class_env:class_env = [
    («Semigroup»,
      (kindType,[],[(
        «mappend»,
        [],Pred [] (Functions [TypeVar 0;TypeVar 0] (TypeVar 0)))]));
    («Monoid»,
      (kindType,[«Semigroup»],[(
        «mempty»,[],Pred [] (TypeVar 0))]));
    («Foldable»,
      (kindArrow kindType kindType,[],[
       (* Monoid m => (a -> m) -> t a -> m *)
       («foldMap»,[kindType;kindType],
          Pred [(«Monoid»,TypeVar 2)] $
          Functions [Functions [TypeVar 1] (TypeVar 2);
            Cons (TypeVar 0) (TypeVar 1)] (TypeVar 2));
       («toList»,[kindType], Pred [] $
          Functions [Cons (TypeVar 0) (TypeVar 1)] (Cons (UserType 0)
          (TypeVar 1)))]))]
End

Definition test_defaults_def:
  test_defaults:'a default_impls = [«toList»,
    App (Var [] «foldMap») [Lam [«x»,NONE] $
      (Prim (Cons «::») [Var [] «x»;Prim (Cons «[]») []])
    ]
  ]
End

Definition test_defaults_elaborated_def:
  test_defaults_elaborated:Kind list default_impls = [«toList»,
    App (Var [«Foldable»,TypeVar 0;«Monoid»,Cons (UserType 0) (TypeVar 1)] «foldMap») [Lam [«x»,NONE] $
      (Prim (Cons «::») [Var [] «x»;Prim (Cons «[]») []])
    ]
  ]
End

Definition test_instance_env_def:
  test_instance_env = [
    ((«Semigroup»,0n,Atom $ PrimTy Integer),[],
      [«mappend»,typeclass_texp$Lam [«x»,NONE;«y»,NONE]
        (Prim (AtomOp Add) [Var [] «x»;Var [] «y»])]);
    ((«Monoid»,0,Atom $ PrimTy Integer),[],
      [«mempty»,Prim (AtomOp (Lit (Int 0))) []]);
    ((«Foldable»,0,UserType 0),[],
      [«foldMap»,typeclass_texp$Lam [«f»,NONE;«t»,NONE] $
          typeclass_texp$NestedCase (Var [] «t») «t»
            (cepatCons «::» [cepatVar «h»;cepatVar «tl»])
              (App (Var [] «mappend») [
                App (Var [] «f») [Var [] «h»];
                App (Var [] «foldMap») [Var [] «f»;Var [] «tl»]])
            [cepatUScore,Var [] «mempty»]]);
    ((«Semigroup»,1,Cons (UserType 0) (TypeVar 0)),[],
      [«mappend»,Var [] «append»]);
    ((«Monoid»,1,Cons (UserType 0) (TypeVar 0)),[],
      [«mempty»,Prim (Cons «[]») []]);
    ((«Monoid»,2,
      Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1)),
      [«Monoid»,TypeVar 0;«Monoid»,TypeVar 1],
      [«mempty»,Prim (Cons «»)
        [Var [] «mempty»;Var [] «mempty»]]);
    ((«Semigroup»,2,
      Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1)),
      [«Semigroup»,TypeVar 0;«Semigroup»,TypeVar 1],
      [«mappend»,Lam [«x»,NONE;«y»,NONE] $
          typeclass_texp$NestedCase
            (Prim (Cons «») [Var [] «x»;Var [] «y»]) «p»
            (cepatCons «» [
              cepatCons «» [cepatVar «x1»;cepatVar «x2»];
              cepatCons «» [cepatVar «y1»;cepatVar «y2»]])
              (Prim (Cons «») [
                App (Var [] «mappend»)
                  [Var [] «x1»;Var [] «y1»];
                App (Var [] «mappend»)
                  [Var [] «x2»;Var [] «y2»]])
            []])
  ]
End

Definition test_instance_env_elaborated_def:
  test_instance_env_elaborated = [
    ((«Semigroup»,[],Atom $ PrimTy Integer),[],
      [«mappend»,typeclass_texp$Lam [«x»,NONE;«y»,NONE]
        (Prim (AtomOp Add) [Var [] «x»;Var [] «y»])]);
    ((«Monoid»,[],Atom $ PrimTy Integer),[],
      [«mempty»,Prim (AtomOp (Lit (Int 0))) []]);
    ((«Foldable»,[],UserType 0),[],
      [«foldMap»,typeclass_texp$Lam [«f»,NONE;«t»,NONE] $
          typeclass_texp$NestedCase (Var [] «t») «t»
            (cepatCons «::» [cepatVar «h»;cepatVar «tl»])
              (App (Var [(«Semigroup»,TypeVar 1)] «mappend») [
                App (Var [] «f») [Var [] «h»];
                App (Var [
                    («Foldable»,UserType 0);
                    («Monoid»,TypeVar 1)] «foldMap»)
                  [Var [] «f»;Var [] «tl»]])
            [cepatUScore,Var [(«Monoid»,TypeVar 1)] «mempty»]]);
    ((«Semigroup»,[kindType],Cons (UserType 0) (TypeVar 0)),[],
      [«mappend»,Var [] «append»]);
    ((«Monoid»,[kindType],Cons (UserType 0) (TypeVar 0)),[],
      [«mempty»,Prim (Cons «[]») []]);
    ((«Monoid»,[kindType;kindType],
      Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1)),
      [«Monoid»,TypeVar 0;«Monoid»,TypeVar 1],
      [«mempty»,Prim (Cons «»)
        [Var [«Monoid»,TypeVar 0] «mempty»;
         Var [«Monoid»,TypeVar 1] «mempty»]]);
    ((«Semigroup»,[kindType;kindType],
      Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1)),
      [«Semigroup»,TypeVar 0;«Semigroup»,TypeVar 1],
      [«mappend»,Lam [«x»,NONE;«y»,NONE] $
          typeclass_texp$NestedCase
            (Prim (Cons «») [Var [] «x»;Var [] «y»]) «p»
            (cepatCons «» [
              cepatCons «» [cepatVar «x1»;cepatVar «x2»];
              cepatCons «» [cepatVar «y1»;cepatVar «y2»]])
              (Prim (Cons «») [
                App (Var [«Semigroup»,TypeVar 0] «mappend»)
                  [Var [] «x1»;Var [] «y1»];
                App (Var [«Semigroup»,TypeVar 1] «mappend»)
                  [Var [] «x2»;Var [] «y2»]])
            []])
  ]
End

Definition test_prog_def:
  test_prog = [
    («append»,NONE),Lam [«l»,NONE;«r»,NONE] $
    NestedCase (Var [] «l») «l»
      (cepatCons «::» [cepatVar «h»; cepatVar «tl»])
        (Prim (Cons «::») [Var [] «h»;
          App (Var [] «append») [Var [] «tl»; Var [] «r»]])
      [cepatCons «[]» [],Var [] «r»];

    («test»,NONE),
      Letrec [(«fold»,NONE),
        App (Var [] «foldMap») [Lam [«x»,NONE] (Var [] «x»)]] $
      App (Var [] «fold») [App (Var [] «fold»)
        [App (Var [] «toList») [Prim (Cons «::») [
          Prim (Cons «::») [
            Prim (Cons «») [
              Prim (AtomOp $ Lit (Int 1)) [];
              Prim (AtomOp $ Lit (Int 1)) []];
            Prim (Cons «[]») []];
          Prim (Cons «[]») []]]]]
  ]
End

Definition test_prog_elaborated_def:
  test_prog_elaborated = [
    («append»,SOME ([kindType],
      Pred [] $ Functions [
        Cons (UserType 0) (TypeVar 0);
        Cons (UserType 0) (TypeVar 0)] $
        Cons (UserType 0) (TypeVar 0))),
    Lam [«l»,NONE;«r»,NONE] $
      NestedCase (Var [] «l») «l»
      (cepatCons «::» [cepatVar «h»; cepatVar «tl»])
        (Prim (Cons «::») [Var [] «h»;
          App (Var [] «append») [Var [] «tl»; Var [] «r»]])
      [cepatCons «[]» [],Var [] «r»];

    («test»,
      SOME ([],Pred [] $
        Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
          (Atom $ PrimTy Integer))),
      typeclass_texp$Letrec [(«fold»,
        SOME (
          [kindArrow kindType kindType;kindType],
          Pred [(«Foldable»,TypeVar 0);(«Monoid»,TypeVar 1)] $
            Functions [Cons (TypeVar 0) (TypeVar 1)] (TypeVar 1))),
        typeclass_texp$App
          (Var [(«Foldable»,TypeVar 0);(«Monoid»,TypeVar 1)] «foldMap»)
          [Lam [«x»,NONE] (Var [] «x»)]] $
      typeclass_texp$App
        (Var [
          «Foldable»,UserType 0;
          «Monoid»,
            Cons (Cons (Tup 2) (Atom $ PrimTy Integer)) $
              Atom $ PrimTy Integer]
          «fold») [
        typeclass_texp$App
          (Var [
            «Foldable»,UserType 0;
            «Monoid»,
              Cons (UserType 0) $
                Cons (Cons (Tup 2) $ Atom $ PrimTy Integer) $
                  Atom $ PrimTy Integer]
            «fold»)
          [App (Var [«Foldable»,UserType 0] «toList»)
            [Prim (Cons «::») [
              Prim (Cons «::») [
                Prim (Cons «») [
                  Prim (AtomOp $ Lit (Int 1)) [];
                  Prim (AtomOp $ Lit (Int 1)) []];
                Prim (Cons «[]») []];
              Prim (Cons «[]») []]
            ]
          ]
        ]
  ]
End

Triviality UNIQUE_MEMBER_SUBSET_SING:
  (∀x. x ∈ s ⇒ x = y) ⇔ s ⊆ {y}
Proof
  rw[EQ_IMP_THM,SUBSET_DEF]
QED

Theorem test_instance_env_type_check:
  ie = set (class_env_to_ie test_class_env ++
    instance_env_to_ie test_instance_env_elaborated) ∧
  env = [
    «test»,[],Pred [] $
      Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
        (Atom $ PrimTy Integer);
    «append»,[kindType],Pred [] $
      Functions [
        Cons (UserType 0) (TypeVar 0);
        Cons (UserType 0) (TypeVar 0)] $
        Cons (UserType 0) (TypeVar 0)] ++
    class_env_to_env test_class_env ⇒
  type_elaborate_inst_env initial_namespace test_class_env
    (ce_to_clk test_class_env) ie st env
    test_instance_env test_instance_env_elaborated
Proof
  rw[type_elaborate_inst_env_def] >>
  CONV_TAC (RATOR_CONV $ SCONV[test_instance_env_def]) >>
  CONV_TAC (RAND_CONV $ SCONV[test_instance_env_elaborated_def]) >>
  rw[]
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >-
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def] >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[type_ok_def,kind_ok_def,kind_wf_Prim,PULL_EXISTS] >>
    irule_at (Pos hd) type_elaborate_texp_AtomOp >>
    simp[LIST_REL3_simp,PULL_EXISTS] >>
    irule_at (Pos last) type_atom_op_IntOps_Int >>
    simp[] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[has_dicts_simp,specialises_pred_def,subst_db_pred_def] >>
    simp[oneline get_PrimTys_def,AllCaseEqs()]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >-
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def] >>
    irule_at (Pos hd) type_elaborate_texp_AtomOp >>
    irule_at (Pos last) type_atom_op_Lit >>
    simp[type_lit_rules,get_PrimTys_def,LIST_REL3_simp]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- (
      simp[pred_type_well_scoped_def] >>
      simp[collect_type_vars_def,Functions_def]) >>
    simp[] >>
    conj_tac >- (
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def,
        LLOOKUP_THM] >>
      simp[typedefs_to_cdb_def,initial_namespace_def,
        LLOOKUP_THM,kind_arrows_def,
        test_class_env_def,ce_to_clk_def]) >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    rw[type_ok_def,kind_ok_def,PULL_EXISTS,LLOOKUP_THM] >>
    rw[GSYM PULL_EXISTS]
    >- simp[Functions_def,LLOOKUP_THM]
    >- simp[LLOOKUP_THM,typedefs_to_cdb_def,
        initial_namespace_def,kind_arrows_def] >>
    qrefinel [`Functions args_t ret_t`,`Cons (UserType 0) (TypeVar 0)`] >>
    irule_at (Pos hd) type_elaborate_texp_NestedCase >>
    irule_at (Pos hd) type_elaborate_texp_Var >>
    simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
      PULL_EXISTS] >>
    irule_at (Pos hd) type_cepat_Cons >>
    simp[Once initial_namespace_def,destruct_type_cons_def,
      subst_db_def,split_ty_cons_def,split_ty_cons_aux_def,
      type_cons_def,LLOOKUP_THM,kind_ok_def,LIST_REL3_simp,
      PULL_EXISTS] >>
    rpt (irule_at Any type_cepat_Var) >>
    rpt (irule_at Any type_cepat_UScore) >>
    irule_at Any type_elaborate_texp_Var >>
    simp[Once class_env_to_env_def,Once test_class_env_def] >>
    simp[specialises_pred_def,get_method_type_def,subst_db_pred_def] >>
    simp[PULL_EXISTS,subst_db_def,kind_ok_def,LLOOKUP_THM,has_dicts_simp] >>
    irule_at (Pos last) exhaustive_cepat_UScore >>
    rw[GSYM PULL_EXISTS]
    >- (irule has_dict_lie >> simp[]) >>
    irule_at (Pos hd) type_elaborate_texp_App >>
    irule_at (Pos hd) type_elaborate_texp_Var >>
    simp[Once class_env_to_env_def,Once test_class_env_def] >>
    simp[specialises_pred_def,get_method_type_def,has_dicts_simp] >>
    simp[PULL_EXISTS,subst_db_def,subst_db_pred_def,
    subst_db_Functions,kind_ok_def,LLOOKUP_THM,LIST_REL3_simp] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    rw[GSYM PULL_EXISTS]
    >- (
      irule has_dict_ie >>
      qexistsl [
        `[(«Monoid»,TypeVar 1)]`,
        `Entail [kindType] [(«Monoid»,TypeVar 0)] («Semigroup»,TypeVar 0)`] >>
      simp[Once class_env_to_ie_def,Once test_class_env_def,
        class_to_entailments_def] >>
      simp[specialises_inst_def,PULL_EXISTS,subst_db_def] >>
      simp[kind_ok_def,LLOOKUP_THM,has_dicts_simp] >>
      irule has_dict_lie >>
      simp[]) >>
    rpt (irule_at Any type_elaborate_texp_App) >>
    simp[LIST_REL3_simp] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[specialises_pred_def,PULL_EXISTS,subst_db_pred_def,
      subst_db_Functions,has_dicts_empty,
      has_dicts_simp,LIST_REL3_simp] >>
    simp[Once class_env_to_env_def,Once test_class_env_def] >>
    irule_at (Pos hd) $ iffLR FUN_EQ_THM >>
    qrefine `[_]` >>
    simp[] >>
    irule_at (Pos hd) EQ_REFL >>
    simp[get_method_type_def,subst_db_Functions,PULL_EXISTS,kind_ok_def,
      specialises_pred_def,subst_db_def,subst_db_pred_def,LLOOKUP_THM,
      GSYM Functions_APPEND] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[Once typedefs_to_cdb_def,Once initial_namespace_def,LLOOKUP_THM] >>
    simp[Once initial_namespace_def,kind_arrows_def] >>
    rw[]
    >- (
      irule has_dict_ie >>
      simp[instance_env_to_ie_def,instance_to_entailment_def,
        test_instance_env_elaborated_def] >>
      qexistsl [`[]`,`Entail [] [] («Foldable»,UserType 0)`] >>
      simp[has_dicts_empty,specialises_inst_def,subst_db_def,MEM_MAP]
    ) >>
    irule has_dict_lie >>
    simp[]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >- (
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def,LLOOKUP_THM] >>
      simp[typedefs_to_cdb_def,initial_namespace_def,
        LLOOKUP_THM,kind_arrows_def]) >>
    irule type_elaborate_texp_Var >>
    simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
      subst_db_def,subst_db_Functions,PULL_EXISTS] >>
    simp[Functions_def,kind_ok_def,LLOOKUP_THM]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >- (
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        kind_wf_Functions,subst_db_def,shift_db_def] >>
      simp[typedefs_to_cdb_def,initial_namespace_def,
        LLOOKUP_THM,kind_arrows_def]) >>
    irule type_elaborate_texp_Cons >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexistsl [`0`,`[TypeVar 0]`] >>
    simp[type_cons_def,tcons_to_type_def,cons_types_def,
      type_ok_def,kind_ok_def,LIST_REL3_simp] >>
    simp[LLOOKUP_THM,initial_namespace_def]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    simp[pred_type_kind_ok_def,pred_kind_wf_def,
      kind_wf_Functions,subst_db_def,shift_db_def,
      LLOOKUP_THM,kind_arrows_def] >>
    irule type_elaborate_texp_Tuple >>
    simp[LIST_REL3_simp,PULL_EXISTS,cons_types_def] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[has_dicts_simp,test_class_env_def,
      class_env_to_env_def,specialises_pred_def,
      subst_db_pred_def,subst_db_Functions,
      subst_db_def,get_method_type_def,PULL_EXISTS] >>
    simp[kind_ok_def,LLOOKUP_THM] >>
    rpt (irule_at Any has_dict_lie) >>
    simp[]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    simp[pred_type_kind_ok_def,pred_kind_wf_def,
      kind_wf_Functions,subst_db_def,shift_db_def,
      LLOOKUP_THM,kind_arrows_def] >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[type_ok_def,kind_ok_def,PULL_EXISTS,
      kind_arrows_def,LLOOKUP_THM] >>
    irule_at (Pos hd) type_elaborate_texp_NestedCase >>
    simp[] >>
    rpt (irule_at Any type_elaborate_texp_Tuple) >>
    simp[cons_types_def,LIST_REL3_simp,PULL_EXISTS] >>
    rpt (
      irule_at Any type_cepat_Cons >>
      simp[LIST_REL3_simp,PULL_EXISTS]
    ) >>
    rpt (irule_at Any type_cepat_Var) >>
    qrefinel [
      `Cons (Cons (Tup 2) (TypeVar a)) (TypeVar b)`,
      `Cons (Cons (Tup 2) (TypeVar a)) (TypeVar b)`] >>
    simp[destruct_type_cons_def,split_ty_cons_def,
      split_ty_cons_aux_def,initial_namespace_def] >>
    rpt (irule_at Any type_elaborate_texp_App) >>
    simp[LIST_REL3_simp,PULL_EXISTS] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[class_env_to_env_def,test_class_env_def,get_method_type_def,
      has_dicts_simp] >>
    simp[specialises_pred_def,subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def,PULL_EXISTS,
      subst_db_def,shift_db_def] >>
    rpt (irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL) >>
    simp[kind_ok_def,LLOOKUP_THM] >>
    rpt (irule_at Any has_dict_lie) >>
    simp[] >>
    irule_at Any exhaustive_cepat_Cons >>
    simp[PULL_EXISTS,destruct_type_cons_def,
      split_ty_cons_def,split_ty_cons_aux_def] >>
    qexists `{[cepatCons «» [cepatVar «x1»; cepatVar «x2»];
      cepatCons «» [cepatVar «y1»; cepatVar «y2»]]}` >>
    rpt (irule_at Any exhaustive_cepat_List) >>
    irule_at Any exhaustive_cepat_Nil >>
    simp[] >>
    irule_at (Pos last) $ cj 1 $ iffLR SET_EQ_SUBSET >>
    simp[IMAGE_DEF,Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
    simp[FORALL_AND_THM,GSYM CONJ_ASSOC] >>
    simp[LAMBDA_PROD,GSYM PEXISTS_THM,GSYM PFORALL_THM] >>
    ntac 2 (
      irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[]) >>
    irule_at (Pat `_ ⊆ _`) $ cj 1 $ iffLR SET_EQ_SUBSET >>
    simp[EXTENSION,EQ_IMP_THM,PULL_EXISTS,FORALL_AND_THM] >>
    simp[GSYM CONJ_ASSOC] >>
    irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[] >>
    ntac 2 $ irule_at
      (Pat `exhaustive_cepat _ _ _ {cepatCons «» [_;_]}`)
      exhaustive_cepat_Cons >>
    simp[PULL_EXISTS,destruct_type_cons_def,
      split_ty_cons_def,split_ty_cons_aux_def] >>
    rpt (irule_at Any $ cj 1 $ iffLR SET_EQ_SUBSET) >>
    simp[IMAGE_DEF,EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
    simp[FORALL_AND_THM,GSYM CONJ_ASSOC] >>
    simp[LAMBDA_PROD,GSYM PEXISTS_THM,GSYM PFORALL_THM] >>
    rpt (irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[]) >>
    rpt (irule_at Any exhaustive_cepat_List) >>
    rpt (irule_at Any exhaustive_cepat_Nil) >>
    simp[] >>
    rpt (irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[]) >>
    rpt $ irule_at (Pat `_ ⊆ _`) $ cj 1 $ iffLR SET_EQ_SUBSET >>
    simp[EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
    simp[FORALL_AND_THM,LAMBDA_PROD,
      GSYM PFORALL_THM,GSYM PEXISTS_THM] >>
    rpt (irule_at Any exhaustive_cepat_Var) >>
    rpt (irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[])
  )
QED

Theorem test_defaults_type_check:
  ie = set (class_env_to_ie test_class_env ++
    instance_env_to_ie test_instance_env_elaborated) ∧
  env = [
    «test»,[],Pred [] $
      Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
        (Atom $ PrimTy Integer);
    «append»,[kindType],Pred [] $
      Functions [
        Cons (UserType 0) (TypeVar 0);
        Cons (UserType 0) (TypeVar 0)] $
        Cons (UserType 0) (TypeVar 0)] ++
    class_env_to_env test_class_env ⇒

  type_elaborate_default_impls test_class_env initial_namespace
    (ce_to_clk test_class_env) ie st env
    test_defaults test_defaults_elaborated
Proof
  rw[test_defaults_def,test_defaults_elaborated_def,
    type_elaborate_default_impls_def,type_elaborate_default_impl_def] >>
  simp[Once test_class_env_def] >>
  qexists `«Foldable»` >> simp[] >>
  irule type_elaborate_texp_Pred >>
  simp[pred_type_well_scoped_def,pred_type_kind_ok_def,
    pred_kind_wf_def,collect_type_vars_def,Once Functions_def] >>
  simp[Once Functions_def,LLOOKUP_THM] >>
  simp[Once Functions_def,LLOOKUP_THM,
    Once typedefs_to_cdb_def,Once initial_namespace_def] >>
  simp[Once initial_namespace_def,Once test_class_env_def,
    kind_arrows_def,ce_to_clk_def] >>
  irule type_elaborate_texp_App >>
  simp[LIST_REL3_simp,PULL_EXISTS,GSYM Functions_APPEND] >>
  irule_at (Pos last) type_elaborate_texp_Var >>
  simp[Once class_env_to_env_def,Once test_class_env_def,
    get_method_type_def,has_dicts_simp,LIST_REL3_simp,
    PULL_EXISTS,specialises_pred_def,subst_db_pred_def,kind_ok_def,
    subst_db_Functions,subst_db_def] >>
  irule_at (Pos last) type_elaborate_texp_Lam >>
  irule_at (Pat `type_elaborate_texp`) type_elaborate_texp_Cons >>
  simp[LIST_REL3_simp,PULL_EXISTS] >>
  irule_at (Pat `type_elaborate_texp`) type_elaborate_texp_Var >>
  simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
    subst_db_def] >>
  irule_at (Pat `type_elaborate_texp`) type_elaborate_texp_Cons >>
  simp[LIST_REL3_simp,PULL_EXISTS,type_cons_def] >>
  qexistsl [`0`,`0`] >>
  simp[LLOOKUP_THM,initial_namespace_def,PULL_EXISTS,typedefs_to_cdb_def,
    tcons_to_type_def,cons_types_def,subst_db_def,
    kind_arrows_def] >>
  irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
  rw[kind_ok_def,type_ok_def,LLOOKUP_THM]
  >- (irule has_dict_lie >> simp[]) >>
  irule has_dict_ie >>
  CONV_TAC (RESORT_EXISTS_CONV rev) >>
  qexists `Entail [kindType] [] («Monoid»,Cons (UserType 0) (TypeVar 0))`>>
  simp[instance_env_to_ie_def,instance_to_entailment_def,has_dicts_simp,
    test_instance_env_elaborated_def,PULL_EXISTS,kind_ok_def,
    specialises_inst_def,subst_db_def,LLOOKUP_THM]
QED

Theorem test_prog_type_check:
  ie = set (class_env_to_ie test_class_env ++
    instance_env_to_ie test_instance_env_elaborated) ∧
  OPT_MMAP (SND o FST) test_prog_elaborated = SOME fns_type_scheme ∧
  env = REVERSE (ZIP (MAP (FST o FST) test_prog,fns_type_scheme)) ++
    class_env_to_env test_class_env ⇒
  type_elaborate_bindings initial_namespace (ce_to_clk test_class_env) ie
    EMPTY [] st env
    test_prog test_prog_elaborated
Proof
  rw[type_elaborate_bindings_def,test_prog_def,test_prog_elaborated_def]
  >- (
    irule type_elaborate_texp_Pred >>
    simp[pred_type_well_scoped_def,pred_type_kind_ok_def,pred_kind_wf_def] >>
    conj_tac
    >- simp[Functions_def,LLOOKUP_THM,
        typedefs_to_cdb_def,kind_arrows_def,
        initial_namespace_def] >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[PULL_EXISTS,type_ok_def,kind_ok_def, LLOOKUP_THM] >>
    rw[GSYM PULL_EXISTS]
    >- simp[typedefs_to_cdb_def,kind_arrows_def,
      LLOOKUP_THM,initial_namespace_def] >>
    irule_at (Pos hd) type_elaborate_texp_NestedCase >>
    qexists `Cons (UserType 0) (TypeVar 0)` >>
    irule_at (Pos hd) type_elaborate_texp_Var >>
    simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,PULL_EXISTS] >>
    irule_at (Pos hd) type_cepat_Cons >>
    simp[Once initial_namespace_def,destruct_type_cons_def,
      split_ty_cons_def,split_ty_cons_aux_def,type_cons_def,
      LIST_REL3_simp,LLOOKUP_THM,kind_ok_def,PULL_EXISTS,
      subst_db_def] >>
    rpt $ irule_at Any type_cepat_Var >>
    irule_at Any type_cepat_Cons >>
    simp[Once initial_namespace_def,destruct_type_cons_def,
      split_ty_cons_def,split_ty_cons_aux_def,type_cons_def,
      LLOOKUP_THM,kind_ok_def,LIST_REL3_simp] >>
    irule_at (Pat `exhaustive_cepat`) exhaustive_cepat_Cons >>
    rw[Once $ GSYM PULL_EXISTS]
    >- (
      gvs[initial_namespace_def,destruct_type_cons_def,
        split_ty_cons_def,split_ty_cons_aux_def,type_cons_def,
        LLOOKUP_THM,PULL_EXISTS,AllCaseEqs()]
      >- (
        irule_at (Pos hd) exhaustive_cepat_Nil >>
        simp[SUBSET_SING,LEFT_AND_OVER_OR,EXISTS_OR_THM] >>
        qexists `{[]}` >>
        simp[]) >>
      rpt (irule_at (Pat `exhaustive_cepatl`) exhaustive_cepat_List) >>
      irule_at Any exhaustive_cepat_Nil >>
      simp[IMAGE_DEF,ELIM_UNCURRY,SUBSET_DEF,PULL_EXISTS] >>
      simp[LAMBDA_PROD,GSYM PFORALL_THM] >>
      rpt (irule_at Any exhaustive_cepat_Var) >>
      simp[UNIQUE_MEMBER_SUBSET_SING] >>
      irule_at (Pos last) SUBSET_REFL >>
      irule_at (Pos hd) $ iffRL IN_SING >>
      simp[] >>
      irule_at (Pos hd) $ iffRL IN_SING >>
      simp[] >>
      irule_at (Pos hd) $ iffRL IN_SING >>
      simp[IMP_CONJ_THM,FORALL_AND_THM] >>
      simp[UNIQUE_MEMBER_SUBSET_SING] >>
      irule_at (Pos last) SUBSET_REFL >>
      simp[]
    ) >>
    irule_at Any type_elaborate_texp_Var >>
    simp[specialises_pred_def,subst_db_pred_def,
      has_dicts_simp] >>
    irule type_elaborate_texp_Cons >>
    CONV_TAC (RESORT_EXISTS_CONV rev) >>
    qexistsl [`0`,`[TypeVar 0]`] >>
    simp[tcons_to_type_def,type_cons_def,cons_types_def,
      LLOOKUP_THM,subst_db_def,type_ok_def,kind_ok_def,
      LIST_REL3_simp,PULL_EXISTS] >>
    rw[initial_namespace_def]
    >- (
      irule type_elaborate_texp_Var >>
      simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,subst_db_def]) >>
    irule type_elaborate_texp_App >>
    simp[LIST_REL3_simp,PULL_EXISTS] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[has_dicts_simp,specialises_pred_def,subst_db_pred_def,
      shift_db_pred_def,shift_db_Functions,shift_db_def,
      subst_db_Functions,subst_db_def,PULL_EXISTS] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[kind_ok_def,LLOOKUP_THM]
  ) >>
  irule type_elaborate_texp_Pred >>
  rw[pred_type_well_scoped_def,pred_type_kind_ok_def,
    pred_kind_wf_def,kind_arrows_def] >>
  irule type_elaborate_texp_Letrec >>
  simp[LIST_REL3_simp,PULL_EXISTS] >>
  rw[LAMBDA_PROD,GSYM PEXISTS_THM]
  >- (
    irule type_elaborate_texp_Pred >>
    rw[pred_type_kind_ok_def,pred_kind_wf_def,pred_type_well_scoped_def] >>
    simp[collect_type_vars_Functions,collect_type_vars_def]
    >- simp[Functions_def,LLOOKUP_THM]
    >- simp[Functions_def,LLOOKUP_THM,ce_to_clk_def,test_class_env_def]
    >- simp[Functions_def,LLOOKUP_THM,ce_to_clk_def,test_class_env_def] >>
    irule type_elaborate_texp_App >>
    simp[LIST_REL3_simp,PULL_EXISTS,GSYM Functions_APPEND] >>
    irule_at Any type_elaborate_texp_Var >>
    simp[Once class_env_to_env_def,Once test_class_env_def,
      specialises_pred_def,subst_db_pred_def,get_method_type_def,
      shift_db_pred_def,subst_db_Functions,shift_db_Functions,
      subst_db_def,shift_db_def,PULL_EXISTS] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    rw[kind_ok_def,LLOOKUP_THM,has_dicts_simp]
    >- (irule has_dict_lie >> simp[])
    >- (irule has_dict_lie >> simp[])
    >- (
      irule type_elaborate_texp_Lam >>
      irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
      simp[type_ok_def,kind_ok_def,PULL_EXISTS,LLOOKUP_THM] >>
      irule_at (Pos hd) type_elaborate_texp_Var >>
      simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def]
    )
  ) >>
  irule type_elaborate_texp_App >>
  simp[LIST_REL3_simp] >>
  rpt (irule_at Any type_elaborate_texp_App >> simp[LIST_REL3_simp]) >>
  rpt (irule_at Any type_elaborate_texp_Var) >>
  simp[has_dicts_simp,specialises_pred_def,subst_db_pred_def,
    subst_db_def,subst_db_Functions,PULL_EXISTS,kind_ok_def] >>
  rpt $ irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
  simp[GSYM PULL_EXISTS,DISJ_IMP_THM,FORALL_AND_THM,GSYM CONJ_ASSOC,
    kind_arrows_def] >>
  conj_asm1_tac
  >- (
    irule has_dict_ie >>
    qexistsl [`[]`,`Entail [] [] («Foldable»,UserType 0)`] >>
    simp[instance_env_to_ie_def,test_instance_env_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,
      specialises_inst_def]
  ) >>
  `∀(ns:typedefs) db lie. has_dict ns db
    (set (class_env_to_ie test_class_env) ∪
     set (instance_env_to_ie test_instance_env_elaborated)) lie
    («Monoid»,Atom (PrimTy Integer))`
  by (
    rpt strip_tac >>
    irule has_dict_ie >>
    qexistsl [`[]`,`Entail [] [] («Monoid»,Atom (PrimTy Integer))`] >>
    simp[instance_env_to_ie_def,test_instance_env_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,
      specialises_inst_def]
  ) >>
  conj_asm1_tac
  >- (
    irule has_dict_ie >>
    CONV_TAC $ RESORT_EXISTS_CONV rev >>
    qexists `Entail [kindType; kindType]
         [(«Monoid»,TypeVar 0); («Monoid»,TypeVar 1)]
         («Monoid»,Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1))` >>
    simp[Once instance_env_to_ie_def,
      Once test_instance_env_elaborated_def,
      instance_to_entailment_def,has_dicts_simp,kind_ok_def,
      specialises_inst_def,subst_db_def,PULL_EXISTS] >>
    simp[LAMBDA_PROD,GSYM PEXISTS_THM,GSYM PFORALL_THM]
  ) >>
  conj_asm1_tac
  >- simp[typedefs_to_cdb_def,initial_namespace_def,
      kind_arrows_def,LLOOKUP_THM] >>
  rw[]
  >- (
    irule has_dict_ie >>
    qexistsl [`[]`,`Entail [kindType] [] («Monoid»,Cons (UserType 0) (TypeVar 0))`] >>
    simp[instance_env_to_ie_def,test_instance_env_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,subst_db_def,
      specialises_inst_def,PULL_EXISTS,kind_ok_def,
      kind_arrows_def]
  ) >>
  simp[Once class_env_to_env_def,Once test_class_env_def,
    subst_db_def,get_method_type_def,
    specialises_pred_def,subst_db_pred_def,PULL_EXISTS,
    shift_db_pred_def,subst_db_Functions,shift_db_Functions,
    shift_db_def] >>
  irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
  simp[kind_ok_def,LLOOKUP_THM,kind_arrows_def] >>
  ntac 2 (
    irule_at Any type_elaborate_texp_Cons >>
    simp[LIST_REL3_simp,PULL_EXISTS]) >>
  irule_at Any type_elaborate_texp_Tuple >>
  rpt (
    irule_at Any type_elaborate_texp_Cons >>
    simp[LIST_REL3_simp,PULL_EXISTS]) >>
  simp[initial_namespace_def,typedefs_to_cdb_def,kind_arrows_def,
    type_cons_def,tcons_to_type_def,cons_types_def,subst_db_def,
    LIST_REL3_simp,PULL_EXISTS,LLOOKUP_THM,kind_ok_def] >>
  irule type_elaborate_texp_AtomOp >>
  simp[LIST_REL3_simp,get_PrimTys_def] >>
  irule type_atom_op_Lit >>
  simp[type_lit_rules]
QED

Theorem test_whole_prog_type_check:
  type_elaborate_prog initial_namespace test_class_env st
    test_defaults test_instance_env test_prog
    test_defaults_elaborated test_instance_env_elaborated
    test_prog_elaborated
Proof
  simp[type_elaborate_prog_def] >>
  irule_at Any test_prog_type_check >>
  irule_at Any test_instance_env_type_check >>
  irule_at Any test_defaults_type_check >>
  simp[test_prog_elaborated_def,test_prog_def] >>
  simp[instance_env_kind_check_def,pred_type_kind_ok_def,
    pred_kind_wf_def,Functions_def,LLOOKUP_THM] >>
  rw[test_instance_env_def,test_instance_env_elaborated_def,
    test_class_env_def,ce_to_clk_def,LLOOKUP_THM,
    instance_kind_check_def,kind_ok_def,kind_arrows_def,
    initial_namespace_def,typedefs_to_cdb_def]
QED

Definition test_cl_cons_def:
  test_cl_cons = [
    «Semigroup»,«SemigroupDict»;
    «Monoid»,«MonoidDict»;
    «Foldable»,«FoldableDict»
  ]
End

Definition test_sup_vs_def:
  test_sup_vs = [«getSemigroup»]
End

Definition test_inst_vs_def:
  test_inst_vs = [
    «semigroupInt»;
    «monoidInt»;
    «foldableList»;
    «semigroupList»;
    «monoidList»;
    «monoidTuple»;
    «semigroupTuple»
  ]
End

Definition test_default_name_map_def:
  test_default_name_map = [«toList»,«default_toList»]
End

Definition test_cl_to_tyid_def:
  test_cl_to_tyid = FEMPTY |++
    ZIP (MAP FST test_class_env,
      GENLIST (λn. n + LENGTH (SND initial_namespace))
        (LENGTH test_class_env))
End

Theorem test_cl_to_tyid = EVAL ``test_cl_to_tyid``;

Theorem test_class_env_to_ns =
  EVAL ``class_env_to_ns test_class_env test_cl_to_tyid
    (MAP SND test_cl_cons) test_class_env``;

Definition test_namespace_translated_def:
  test_namespace_translated =
    append_ns
      (namespace_to_tcexp_namespace initial_namespace)
      ([],THE $ class_env_to_ns
          test_class_env test_cl_to_tyid
          (MAP SND test_cl_cons) test_class_env)
End

Theorem test_namespace_translated =
  EVAL ``test_namespace_translated``;

Definition test_class_env_translated_def:
  test_class_env_translated =
    class_env_construct_dict (MAP SND test_cl_cons) test_sup_vs
      test_class_env
End

Theorem test_class_env_translated =
  EVAL ``test_class_env_translated``;

Definition test_ie_map_def:
  test_ie_map = FEMPTY |++
   (ZIP (test_sup_vs,class_env_to_ie test_class_env) ++
    ZIP (test_inst_vs,
      instance_env_to_ie test_instance_env_elaborated))
End

Theorem test_ie_map = EVAL ``test_ie_map``;

Definition test_env_def:
  test_env =
    set (MAP (FST ∘ FST) test_prog_elaborated ++
      MAP FST (class_env_to_env test_class_env))
End

Theorem test_class_env_to_env =
  EVAL ``class_env_to_env test_class_env``;

Theorem test_env = EVAL ``test_env``;

Definition test_defaults_translated_def:
  test_defaults_translated = [«default_toList»,
    Lam () [«y»] $
      App ()
        (App () (Var () «foldMap») [Var () «y»;Var () «monoidList»])
        [Lam () [«x»] $
          (Prim () (Cons «::») [Var () «x»;Prim () (Cons «[]») []])]
  ]
End

Theorem test_defaults_construct_dict:
  default_impls_construct_dict initial_namespace test_class_env
    test_ie_map test_env test_default_name_map test_defaults_elaborated
    test_defaults_translated
Proof
  simp[default_impls_construct_dict_def] >>
  simp[test_defaults_elaborated_def,test_defaults_translated_def,
    test_default_name_map_def] >>
  qexists `«Foldable»` >>
  simp[Once test_class_env_def] >>
  simp[default_impl_construct_dict_def] >>
  irule texp_construct_dict_Pred >>
  simp[LENGTH_EQ_NUM_compute,PULL_EXISTS] >>
  simp[test_ie_map,test_env,get_names_namespace_def,
    initial_namespace_def,lambda_vars_def] >>
  simp[SmartLam_EQ_Lam_cases] >>
  conj_tac >- EVAL_TAC >>
  irule texp_construct_dict_App >>
  rw[]
  >- (
    irule texp_construct_dict_Lam >>
    simp[] >>
    irule texp_construct_dict_Prim >>
    rw[]
    >- (
      irule texp_construct_dict_Var >>
      simp[construct_dicts_simp]
    ) >>
    irule texp_construct_dict_Prim >>
    simp[]
  ) >>
  irule texp_construct_dict_Var >>
  rw[construct_dicts_simp,PULL_EXISTS]
  >- (
    irule construct_dict_lie >>
    simp[alistTheory.FLOOKUP_FUPDATE_LIST]
  ) >>
  irule construct_dict_ie >>
  simp[construct_dicts_simp,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[specialises_inst_def,PULL_EXISTS,subst_db_def,
    kind_ok_def,LLOOKUP_THM]
QED

Definition test_prog_translated_def:
    test_prog_translated = [
    («append»,
      Lam () [«l»;«r»] $
        NestedCase () (Var () «l») «l»
        (cepatCons «::» [cepatVar «h»; cepatVar «tl»])
          (Prim () (Cons «::») [Var () «h»;
            App () (Var () «append») [Var () «tl»; Var () «r»]])
        [cepatCons «[]» [],Var () «r»]);

    («test»,
      Letrec () [«fold»,
        Lam () [«f0»;«m1»] $ App ()
          (App () (Var () «foldMap»)
            [Var () «f0»;Var () «m1»])
          [Lam () [«x»] (Var () «x»)]] $
      App ()
        (App () (Var () «fold») [
          Var () «foldableList»;
          App () (Var () «monoidTuple»)
            [Var () «monoidInt»;Var () «monoidInt»]]) [
        App ()
          (App () (Var () «fold») [
              Var () «foldableList»;
              Var () «monoidList»])
          [App () (App () (Var () «toList») [Var () «foldableList»])
            [Prim () (Cons «::») [
              Prim () (Cons «::») [
                Prim () (Cons «») [
                  Prim () (AtomOp $ Lit (Int 1)) [];
                  Prim () (AtomOp $ Lit (Int 1)) []];
                Prim () (Cons «[]») []];
              Prim () (Cons «[]») []]
            ]
          ]
        ])
  ]
End

Theorem test_prog_construct_dict:
  LIST_REL (λ((x,ot),e) (y,de).
    x = y ∧
    case ot of
    | NONE => F
    | SOME (new,pt) =>
      pred_texp_construct_dict initial_namespace
        test_ie_map FEMPTY new test_env pt e de)
    test_prog_elaborated test_prog_translated
Proof
  rw[test_prog_elaborated_def,test_prog_translated_def]
  >- (
    irule texp_construct_dict_Pred >>
    simp[] >>
    irule texp_construct_dict_Lam >>
    simp[] >>
    irule texp_construct_dict_NestedCase >>
    simp[] >>
    rpt (irule_at Any texp_construct_dict_Var) >>
    simp[construct_dicts_simp] >>
    irule texp_construct_dict_Prim >>
    simp[] >>
    irule_at Any texp_construct_dict_App >>
    simp[] >>
    rpt (irule_at Any texp_construct_dict_Var) >>
    simp[construct_dicts_simp]
  ) >>
  irule texp_construct_dict_Pred >>
  simp[] >>
  irule texp_construct_dict_Letrec >>
  rw[]
  >- (
    irule texp_construct_dict_Pred >>
    simp[SmartLam_EQ_Lam_cases,PULL_EXISTS,RIGHT_AND_OVER_OR,EXISTS_OR_THM] >>
    disj1_tac >>
    conj_tac >- (
      simp[get_names_namespace_def,initial_namespace_def,
        lambda_vars_def,test_env,test_ie_map,
        finite_mapTheory.FDOM_FUPDATE_LIST] >>
      EVAL_TAC
    ) >>
    irule texp_construct_dict_App >>
    simp[] >>
    irule_at Any texp_construct_dict_Lam >>
    simp[] >>
    irule_at Any texp_construct_dict_Var >>
    simp[construct_dicts_simp] >>
    irule texp_construct_dict_Var >>
    simp[construct_dicts_simp] >>
    rpt (
      irule_at Any construct_dict_lie >>
      simp[alistTheory.FLOOKUP_FUPDATE_LIST])
  ) >>
  rpt (irule_at Any texp_construct_dict_App >> simp[]) >>
  rpt (irule_at Any texp_construct_dict_Prim >> simp[]) >>
  rpt (irule_at Any texp_construct_dict_Var) >>
  simp[construct_dicts_simp] >>
  rpt (irule_at Any construct_dict_ie) >>
  simp[test_ie_map,construct_dicts_simp,
      finite_mapTheory.FLOOKUP_UPDATE,subst_db_def,PULL_EXISTS,
      specialises_inst_def,kind_ok_def,kind_arrows_def] >>
  simp[LAMBDA_PROD,GSYM PEXISTS_THM] >>
  irule construct_dict_ie >>
  simp[finite_mapTheory.FLOOKUP_UPDATE,construct_dicts_simp,
    specialises_inst_def,subst_db_def,PULL_EXISTS]
QED

Definition test_instance_env_translated_def:
  test_instance_env_translated = [
    («semigroupInt», Prim () (Cons «SemigroupDict»)
      [Lam () [«x»;«y»]
        (Prim () (AtomOp Add) [Var () «x»;Var () «y»])]);
    («monoidInt»,Prim () (Cons «MonoidDict»)
      [Var () «semigroupInt»;Prim () (AtomOp (Lit (Int 0))) []]);
    («foldableList»,Prim () (Cons «FoldableDict»)
      [Lam () [«m»;«f»;«t»] (
        NestedCase () (Var () «t») «t»
          (cepatCons «::» [cepatVar «h»;cepatVar «tl»])
            (App ()
              (App () (Var ()  «mappend»)
                [(App () (Var () «getSemigroup») [Var () «m»])]) [
              App () (Var () «f») [Var () «h»];
              App () (
                App () (Var () «foldMap») [
                  (Var () «foldableList»);
                  (Var () «m»)
                ])
                [Var () «f»;Var () «tl»]])
          [cepatUScore,App () (Var () «mempty») [Var () «m»]]);
       App () (Var () «default_toList») [Var () «foldableList»]]);
    («semigroupList»,Prim () (Cons «SemigroupDict») [Var () «append»]);
    («monoidList»,Prim () (Cons «MonoidDict»)
      [Var () «semigroupList»;Prim () (Cons «[]») []]);
    («monoidTuple»,Lam () [«m1»;«m2»] $ Prim () (Cons «MonoidDict») [
      App () (Var () «semigroupTuple») [
        App () (Var () «getSemigroup») [Var () «m1»];
        App () (Var () «getSemigroup») [Var () «m2»]];
      Prim () (Cons «») [
        App () (Var () «mempty») [Var () «m1»];
        App () (Var () «mempty») [Var () «m2»]]]);
    («semigroupTuple»,Lam () [«s1»;«s2»] $ Prim () (Cons «SemigroupDict») [
      Lam () [«x»;«y»] $
        NestedCase ()
          (Prim () (Cons «») [Var () «x»;Var () «y»]) «p»
          (cepatCons «» [
            cepatCons «» [cepatVar «x1»;cepatVar «x2»];
            cepatCons «» [cepatVar «y1»;cepatVar «y2»]])
            (Prim () (Cons «») [
              App ()
                (App () (Var () «mappend») [Var () «s1»])
                [Var () «x1»;Var () «y1»];
              App ()
                (App () (Var () «mappend») [Var () «s2»])
                [Var () «x2»;Var () «y2»]])
          []])
  ]
End

Theorem test_instance_env_construct_dict:
  instance_env_construct_dict initial_namespace test_class_env
    test_ie_map test_env test_cl_cons test_default_name_map
    test_inst_vs test_instance_env_elaborated
    test_instance_env_translated
Proof
  simp[instance_env_construct_dict_def,test_inst_vs_def,LIST_REL3_def,
    test_instance_env_elaborated_def,test_instance_env_translated_def,
    test_class_env_def,test_cl_cons_def,test_default_name_map_def] >>
  rw[instance_construct_dict_def,construct_dicts_simp,PULL_EXISTS]
  >- (
    simp[impl_construct_dict_def,subst_db_pred_def,shift_db_pred_def,
      shift_db_def,subst_db_def,shift_db_Functions,subst_db_Functions] >>
    irule texp_construct_dict_Pred >>
    simp[SmartLam_def] >>
    irule texp_construct_dict_Lam >>
    simp[] >>
    irule texp_construct_dict_Prim >>
    simp[] >>
    rpt (irule_at Any texp_construct_dict_Var) >>
    simp[construct_dicts_simp]
  )
  >- (
    irule construct_dict_ie >>
    simp[test_ie_map,finite_mapTheory.FLOOKUP_UPDATE] >>
    simp[specialises_inst_def,subst_db_def,construct_dicts_simp]
  )
  >- (
    simp[impl_construct_dict_def,subst_db_pred_def,shift_db_pred_def,
      shift_db_def,subst_db_def,shift_db_Functions,subst_db_Functions] >>
    irule texp_construct_dict_Pred >>
    simp[SmartLam_def] >>
    irule texp_construct_dict_Prim >> simp[]
  )
  >- (
    simp[impl_construct_dict_def,subst_db_pred_def,shift_db_pred_def,
      shift_db_def,subst_db_def,shift_db_Functions,subst_db_Functions] >>
    simp[SmartLam_def] >>
    irule texp_construct_dict_Pred >>
    simp[SmartLam_EQ_Lam_cases,RIGHT_AND_OVER_OR,EXISTS_OR_THM] >>
    simp[PULL_EXISTS,LENGTH_EQ_NUM_compute] >>
    conj_tac
    >-  (
      simp[test_ie_map,test_env,lambda_vars_def,
        finite_mapTheory.FDOM_FUPDATE_LIST,
        get_names_namespace_def,initial_namespace_def] >>
      EVAL_TAC
    ) >>
    irule texp_construct_dict_Lam >>
    simp[] >>
    irule texp_construct_dict_NestedCase >>
    simp[] >>
    rpt (irule_at Any texp_construct_dict_App >> simp[]) >>
    rpt (irule_at Any texp_construct_dict_Var) >>
    simp[construct_dicts_simp,PULL_EXISTS] >>
    conj_asm1_tac
    >- (
      irule construct_dict_lie >>
      simp[alistTheory.FLOOKUP_FUPDATE_LIST]
    ) >>
    rw[]
    >- (
      irule construct_dict_ie >>
      simp[Once test_ie_map,finite_mapTheory.FLOOKUP_UPDATE] >>
      simp[specialises_inst_def,PULL_EXISTS,kind_ok_def,subst_db_def] >>
      simp[LAMBDA_PROD,GSYM PEXISTS_THM,LLOOKUP_THM,construct_dicts_simp]
    ) >>
    irule construct_dict_ie >>
    simp[Once test_ie_map,finite_mapTheory.FLOOKUP_UPDATE] >>
    simp[specialises_inst_def,subst_db_def,construct_dicts_simp]
  )
  >- (
    simp[impl_construct_dict_def,subst_db_pred_def,shift_db_pred_def,
      shift_db_def,subst_db_def,shift_db_Functions,subst_db_Functions,
      SmartLam_def] >>
    irule texp_construct_dict_Pred >>
    simp[] >>
    irule texp_construct_dict_Var >>
    simp[construct_dicts_simp]
  )
  >- (
    irule construct_dict_ie >>
    simp[Once test_ie_map,finite_mapTheory.FLOOKUP_UPDATE] >>
    simp[specialises_inst_def,subst_db_def,PULL_EXISTS,kind_ok_def,
      LLOOKUP_THM,construct_dicts_simp]
  )
  >- (
    simp[impl_construct_dict_def,subst_db_pred_def,shift_db_pred_def,
      shift_db_def,subst_db_def,shift_db_Functions,subst_db_Functions,
      SmartLam_def] >>
    irule texp_construct_dict_Pred >>
    simp[] >>
    irule texp_construct_dict_Prim >>
    simp[]
  )
  >- (
    rw[SmartLam_EQ_Lam_cases]
    >- (
      irule construct_dict_ie >>
      simp[Once test_ie_map,finite_mapTheory.FLOOKUP_UPDATE] >>
      simp[specialises_inst_def,subst_db_def,PULL_EXISTS,
        kind_ok_def,LLOOKUP_THM,construct_dicts_simp] >>
      simp[LAMBDA_PROD,GSYM PEXISTS_THM] >>
      rpt (irule_at Any construct_dict_ie) >>
      simp[] >>
      qpat_abbrev_tac `getSemigroupIt = FLOOKUP test_ie_map _` >>
      pop_assum $ mp_tac o
        SRULE[markerTheory.Abbrev_def,test_ie_map,
          finite_mapTheory.FLOOKUP_UPDATE] >>
      disch_then SUBST_ALL_TAC >>
      simp[specialises_inst_def,PULL_EXISTS,subst_db_def,
        kind_ok_def,LLOOKUP_THM] >>
      simp[LAMBDA_PROD,GSYM PEXISTS_THM,construct_dicts_simp] >>
      rpt (irule_at Any construct_dict_lie) >>
      simp[alistTheory.FLOOKUP_FUPDATE_LIST]
    ) >>
    simp[impl_construct_dict_def,subst_db_pred_def,shift_db_pred_def,
      shift_db_def,subst_db_def,shift_db_Functions,subst_db_Functions] >>
    simp[SmartLam_def,dest_Lam_def] >>
    irule texp_construct_dict_Pred >>
    simp[LENGTH_EQ_NUM_compute,PULL_EXISTS] >>
    simp[SmartLam_EQ_Lam_cases] >>
    conj_tac
    >- (
      simp[test_ie_map,test_env,lambda_vars_def,
        finite_mapTheory.FDOM_FUPDATE_LIST,
        get_names_namespace_def,initial_namespace_def] >>
      EVAL_TAC
    ) >>
    irule texp_construct_dict_Prim >>
    simp[] >>
    rpt (irule_at Any texp_construct_dict_Var) >>
    simp[construct_dicts_simp] >>
    rpt (irule_at Any construct_dict_lie) >>
    simp[alistTheory.FLOOKUP_FUPDATE_LIST]
  ) >>
  simp[SmartLam_EQ_Lam_cases,impl_construct_dict_def,
    subst_db_pred_def,shift_db_pred_def,shift_db_def,subst_db_def,
    shift_db_Functions,subst_db_Functions] >>
  simp[SmartLam_def,dest_Lam_def] >>
  irule texp_construct_dict_Pred >>
  simp[SmartLam_EQ_Lam_cases,RIGHT_AND_OVER_OR,EXISTS_OR_THM] >>
  simp[PULL_EXISTS,LENGTH_EQ_NUM_compute] >>
  conj_tac
  >- (
    simp[test_ie_map,test_env,lambda_vars_def,
      finite_mapTheory.FDOM_FUPDATE_LIST,
      get_names_namespace_def,initial_namespace_def] >>
    EVAL_TAC
  ) >>
  irule texp_construct_dict_Lam >>
  simp[] >>
  irule texp_construct_dict_NestedCase >>
  simp[] >>
  rpt (irule_at Any texp_construct_dict_Prim) >> simp[] >>
  rpt (irule_at Any texp_construct_dict_App) >> simp[] >>
  rpt (irule_at Any texp_construct_dict_Var) >>
  simp[construct_dicts_simp] >>
  rpt (irule_at Any construct_dict_lie) >>
  simp[alistTheory.FLOOKUP_FUPDATE_LIST]
QED

Theorem test_whole_prog_construct_dict:
  prog_construct_dict initial_namespace
    test_class_env test_defaults_elaborated
    test_instance_env_elaborated test_prog_elaborated
    test_namespace_translated
    (test_prog_translated ++
      test_defaults_translated ++
      test_instance_env_translated ++
      test_class_env_translated)
Proof
  simp[prog_construct_dict_def] >>
  irule_at (Pos last) $
    SRULE[test_ie_map_def,test_env_def]
    test_prog_construct_dict >>
  simp[GSYM test_ie_map_def,GSYM $ SRULE[] test_env_def] >>
  irule_at Any test_defaults_construct_dict >>
  irule_at Any test_instance_env_construct_dict >>
  PURE_REWRITE_TAC[Once test_class_env_translated_def] >>
  simp[GSYM test_cl_to_tyid_def] >>
  irule_at Any $ GSYM test_class_env_to_ns >>
  simp[class_env_to_env_FST_methods_name] >>
  simp[test_sup_vs_def,test_class_env_def,
    class_env_to_ie_def,LIST_BIND_def,
    rich_listTheory.LENGTH_FLAT,
    class_to_entailments_def] >>
  EVAL_TAC
QED

val _ = export_theory();
