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

Definition test_class_map_def:
  test_class_map:class_map = [
    («Semigroup», <|
      kind := kindType;
      supers := [];
      methods := [
        («mappend»,[],
        PredType [] (Functions [TypeVar 0;TypeVar 0] (TypeVar 0)))];
      constructor := «SemigroupDict» |>);
    («Monoid», <|
      kind := kindType;
      supers := [(«Semigroup»,«getSemigroup»)];
      methods := [(«mempty»,[],PredType [] (TypeVar 0))];
      constructor := «MonoidDict» |>);
    («Foldable», <|
      kind := kindArrow kindType kindType;
      supers := [];
      methods := [
       (* Monoid m => (a -> m) -> t a -> m *)
       (* Monoid 1 => (0 -> 1) -> 2 0 -> 1 *)
       («foldMap»,[kindType;kindType],
          PredType [(«Monoid»,TypeVar 1)] $
          Functions [Functions [TypeVar 0] (TypeVar 1);
            Cons (TypeVar 2) (TypeVar 0)] (TypeVar 1));
       («toList»,[kindType], PredType [] $
          Functions [Cons (TypeVar 1) (TypeVar 0)] (Cons (UserType 0)
          (TypeVar 0)))];
      constructor := «FoldableDict» |>)]
End

Theorem test_class_map_kind_ok:
  class_map_kind_ok (SND initial_namespace) test_class_map
Proof
  rw[class_map_kind_ok_def,initial_namespace_def,
    test_class_map_def,class_map_to_clk_def,
    EVERY_MAP,EVERY_MEM,super_classes_def] >>
  fs[] >>
  rpt $ rw[pred_type_kind_ok_def,kind_wf_Functions,kind_arrows_def,
    pred_kind_wf_def,typedefs_to_cdb_def,oEL_THM]
QED

Definition test_defaults_def:
  test_defaults:'a default_impls = [«toList»,
    App (Var [] «foldMap») [Lam [«x»,NONE] $
      (Prim (Cons «::») [Var [] «x»;Prim (Cons «[]») []])
    ]
  ]
End

Definition test_defaults_elaborated_def:
  test_defaults_elaborated:Kind list default_trans_impls =
  [«toList»,«default_toList»,
    App (Var [«Foldable»,TypeVar 1;«Monoid»,Cons (UserType 0) (TypeVar 0)] «foldMap») [Lam [«x»,NONE] $
      (Prim (Cons «::») [Var [] «x»;Prim (Cons «[]») []])
    ]
  ]
End

Definition test_defaults_types_def:
  test_defaults_types = [([kindType;kindArrow kindType kindType],
      PredType [(«Foldable»,TypeVar 1)] $ Functions [Cons (TypeVar 1) (TypeVar 0)]
         (Cons (UserType 0) (TypeVar 0)))]
End

Definition test_instance_list_def:
  test_instance_list: num instance_list = [
    <| class := «Semigroup»;
       type := Atom $ PrimTy Integer;
       kinds := 0n;
       context := [];
       impls :=  [«mappend»,
         typeclass_texp$Lam [«x»,NONE;«y»,NONE]
         (Prim (AtomOp Add) [Var [] «x»;Var [] «y»])];
       dict_name := «semigroupInt» |>;
    <| class := «Monoid»;
       type := Atom $ PrimTy Integer;
       kinds := 0n;
       context := [];
       impls := [«mempty»,Prim (AtomOp (Lit (Int 0))) []];
       dict_name := «monoidInt» |>;
    <| class := «Foldable»;
       type := UserType 0;
       kinds := 0n;
       context := [];
       impls :=  [«foldMap»,
         typeclass_texp$Lam [«f»,NONE;«t»,NONE] $
          typeclass_texp$NestedCase (Var [] «t») «t»
            (cepatCons «::» [cepatVar «h»;cepatVar «tl»])
              (App (Var [] «mappend») [
                App (Var [] «f») [Var [] «h»];
                App (Var [] «foldMap») [Var [] «f»;Var [] «tl»]])
            [cepatUScore,Var [] «mempty»]];
        dict_name := «foldableList» |>;
    <| class := «Semigroup»;
       type := Cons (UserType 0) (TypeVar 0);
       kinds := 1n;
       context := [];
       impls := [«mappend»,Var [] «append»];
       dict_name := «semigroupList» |>;
    <| class := «Monoid»;
       type := Cons (UserType 0) (TypeVar 0);
       kinds := 1n;
       context := [];
       impls := [«mempty»,Prim (Cons «[]») []];
       dict_name := «monoidList» |>;
    <| class := «Monoid»;
       type := Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1);
       kinds := 2n;
       context := [«Monoid»,TypeVar 0;«Monoid»,TypeVar 1];
       impls := [«mempty»,Prim (Cons «»)
        [Var [] «mempty»;Var [] «mempty»]];
       dict_name := «monoidTuple» |>;
    <| class := «Semigroup»;
       type := Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1);
       kinds := 2n;
       context := [«Semigroup»,TypeVar 0;«Semigroup»,TypeVar 1];
       impls := [«mappend»,Lam [«x»,NONE;«y»,NONE] $
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
            []];
       dict_name := «semigroupTuple»|>
  ]
End

Definition test_instance_list_elaborated_def:
  test_instance_list_elaborated: Kind list instance_list = [
    <| class := «Semigroup»;
       type := Atom $ PrimTy Integer;
       kinds := [];
       context := [];
       impls :=  [«mappend»,
         typeclass_texp$Lam [«x»,NONE;«y»,NONE]
        (Prim (AtomOp Add) [Var [] «x»;Var [] «y»])];
       dict_name := «semigroupInt» |>;
    <| class := «Monoid»;
       type := Atom $ PrimTy Integer;
       kinds := [];
       context := [];
       impls := [«mempty»,Prim (AtomOp (Lit (Int 0))) []];
       dict_name := «monoidInt» |>;
    <| class := «Foldable»;
       type := UserType 0;
       kinds := [];
       context := [];
       impls := [«foldMap»,
        typeclass_texp$Lam [«f»,NONE;«t»,NONE] $
          typeclass_texp$NestedCase (Var [] «t») «t»
            (cepatCons «::» [cepatVar «h»;cepatVar «tl»])
              (App (Var [(«Semigroup»,TypeVar 1)] «mappend») [
                App (Var [] «f») [Var [] «h»];
                App (Var [
                      («Foldable»,UserType 0);
                      («Monoid»,TypeVar 1)] «foldMap»)
                    [Var [] «f»;Var [] «tl»]])
            [cepatUScore,Var [(«Monoid»,TypeVar 1)] «mempty»]];
        dict_name := «foldableList» |>;
    <| class := «Semigroup»;
       type := Cons (UserType 0) (TypeVar 0);
       kinds := [kindType];
       context := [];
       impls := [«mappend»,Var [] «append»];
       dict_name := «semigroupList» |>;
    <| class := «Monoid»;
       type := Cons (UserType 0) (TypeVar 0);
       kinds := [kindType];
       context := [];
       impls := [«mempty»,Prim (Cons «[]») []];
       dict_name := «monoidList» |>;
    <| class := «Monoid»;
       type := Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1);
       kinds := [kindType;kindType];
       context := [«Monoid»,TypeVar 0;«Monoid»,TypeVar 1];
       impls := [«mempty»,Prim (Cons «»)
        [Var [«Monoid»,TypeVar 0] «mempty»;
         Var [«Monoid»,TypeVar 1] «mempty»]];
       dict_name := «monoidTuple» |>;
    <| class := «Semigroup»;
       type := Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1);
       kinds := [kindType;kindType];
       context := [«Semigroup»,TypeVar 0;«Semigroup»,TypeVar 1];
       impls := [«mappend»,Lam [«x»,NONE;«y»,NONE] $
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
            []];
       dict_name := «semigroupTuple»|>
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
      PredType [] $ Functions [
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
      SOME ([],PredType [] $
        Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
          (Atom $ PrimTy Integer))),
      typeclass_texp$Letrec [(«fold»,
        SOME (
          [kindType;kindArrow kindType kindType],
          PredType [(«Foldable»,TypeVar 1);(«Monoid»,TypeVar 0)] $
            Functions [Cons (TypeVar 1) (TypeVar 0)] (TypeVar 0))),
        typeclass_texp$App
          (Var [(«Foldable»,TypeVar 1);(«Monoid»,TypeVar 0)] «foldMap»)
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

Theorem FRANGE_alist_to_fmap_DISJOINT:
  set (MAP FST l) ∩ set (MAP FST r) = ∅ ⇒
  FRANGE (alist_to_fmap (l ++ r)) =
    FRANGE (alist_to_fmap l) ∪ FRANGE (alist_to_fmap r)
Proof
  rw[] >>
  irule finite_mapTheory.FRANGE_FUNION >>
  simp[alistTheory.FDOM_alist_to_fmap,DISJOINT_DEF]
QED

Theorem FRANGE_alist_to_fmap_ALL_DISTINCT:
  ALL_DISTINCT (MAP FST l) ⇒
  FRANGE (alist_to_fmap l) = set (MAP SND l)
Proof
  Induct_on `l` >>
  simp[] >>
  Cases_on `h` >>
  rw[] >>
  `alist_to_fmap l \\ q = alist_to_fmap l`
    suffices_by simp[] >>
  irule finite_mapTheory.DOMSUB_NOT_IN_DOM >>
  simp[alistTheory.FDOM_alist_to_fmap]
QED

Theorem FRANGE_alist_to_fmap_class_map_instance_list:
  FRANGE (alist_to_fmap
      (class_map_to_ie test_class_map ++
       instance_list_to_ie test_instance_list_elaborated)) =
  set (MAP SND (class_map_to_ie test_class_map)) ∪
    set (MAP SND
      (instance_list_to_ie test_instance_list_elaborated))
Proof
  irule EQ_TRANS >>
  irule_at (Pos hd) FRANGE_alist_to_fmap_DISJOINT >>
  DEP_REWRITE_TAC[FRANGE_alist_to_fmap_ALL_DISTINCT] >>
  simp[class_map_to_ie_def,test_class_map_def,
    class_to_entailments_def,instance_list_to_ie_def,
    test_instance_list_elaborated_def,
    instance_to_entailment_def] >>
  EVAL_TAC
QED

Theorem test_instance_list_type_check:
  ie = set (MAP SND (class_map_to_ie test_class_map)) ∪
    set (MAP SND
      (instance_list_to_ie test_instance_list_elaborated)) ∧
  env = [
    «test»,[],PredType [] $
      Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
        (Atom $ PrimTy Integer);
    «append»,[kindType],PredType [] $
      Functions [
        Cons (UserType 0) (TypeVar 0);
        Cons (UserType 0) (TypeVar 0)] $
        Cons (UserType 0) (TypeVar 0)] ++
    class_map_to_env test_class_map ⇒
  type_elaborate_instance_list initial_namespace test_class_map
    ie st env test_instance_list test_instance_list_elaborated
Proof
  rw[type_elaborate_instance_list_def] >>
  CONV_TAC (RATOR_CONV $ SCONV[test_instance_list_def]) >>
  CONV_TAC (RAND_CONV $ SCONV[test_instance_list_elaborated_def]) >>
  rw[type_elaborate_instance_def]
  >- (
    simp[Once test_class_map_def,
      type_elaborate_impls_def,
      type_elaborate_impl_def] >>
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
    simp[Once test_class_map_def,type_elaborate_impls_def,
        type_elaborate_impl_def] >>
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
    simp[Once test_class_map_def,type_elaborate_impls_def,
        type_elaborate_impl_def] >>
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
        test_class_map_def,class_map_to_clk_def]) >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    rw[type_ok_def,kind_ok_def,PULL_EXISTS,LLOOKUP_THM] >>
    rw[GSYM PULL_EXISTS]
    >- simp[Functions_def,LLOOKUP_THM]
    >- simp[LLOOKUP_THM,typedefs_to_cdb_def,
        initial_namespace_def,kind_arrows_def] >>
    irule_at (Pos hd) type_elaborate_texp_NestedCase >>
    irule_at (Pos hd) type_elaborate_texp_Var >>
    simp[has_dicts_empty,specialises_pred_def,
      subst_db_pred_def,PULL_EXISTS] >>
    irule_at (Pos hd) type_cepat_Cons >>
    simp[Once initial_namespace_def,destruct_type_cons_def,
      subst_db_def,split_ty_cons_def,split_ty_cons_aux_def,
      type_cons_def,LLOOKUP_THM,kind_ok_def,LIST_REL3_simp,
      PULL_EXISTS] >>
    rpt (irule_at Any type_cepat_Var) >>
    rpt (irule_at Any type_cepat_UScore) >>
    irule_at Any type_elaborate_texp_Var >>
    simp[Once class_map_to_env_def,Once test_class_map_def] >>
    simp[specialises_pred_def,get_method_type_def,subst_db_pred_def,
      shift_db_pred_def,shift_db_def,subst_db_def] >>
    simp[PULL_EXISTS,kind_ok_def,LLOOKUP_THM,has_dicts_simp] >>
    irule_at (Pos last) exhaustive_cepat_UScore >>
    rw[GSYM PULL_EXISTS]
    >- (irule has_dict_lie >> simp[]) >>
    irule_at (Pos hd) type_elaborate_texp_App >>
    irule_at (Pos hd) type_elaborate_texp_Var >>
    simp[Once class_map_to_env_def,Once test_class_map_def] >>
    simp[specialises_pred_def,get_method_type_def,has_dicts_simp] >>
    simp[PULL_EXISTS,subst_db_def,subst_db_pred_def,shift_db_Functions,
      shift_db_def,shift_db_pred_def,subst_db_Functions,kind_ok_def,
      LLOOKUP_THM,LIST_REL3_simp] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    rw[GSYM PULL_EXISTS]
    >- (
      irule has_dict_ie >>
      qexistsl [
        `[(«Monoid»,TypeVar 1)]`,
        `Entailment [kindType] [(«Monoid»,TypeVar 0)] («Semigroup»,TypeVar 0)`] >>
      simp[Once class_map_to_ie_def,Once test_class_map_def,
        class_to_entailments_def,instance_list_to_ie_def,
        test_instance_list_elaborated_def] >>
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
    simp[Once class_map_to_env_def,Once test_class_map_def] >>
    simp[get_method_type_def,subst_db_Functions,PULL_EXISTS,kind_ok_def,
      specialises_pred_def,subst_db_def,subst_db_pred_def,LLOOKUP_THM,
      GSYM Functions_APPEND,shift_db_def,shift_db_pred_def,shift_db_Functions] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[Once typedefs_to_cdb_def,Once initial_namespace_def,LLOOKUP_THM] >>
    simp[Once initial_namespace_def,kind_arrows_def] >>
    rw[]
    >- (
      irule has_dict_ie >>
      simp[instance_list_to_ie_def,instance_to_entailment_def,
        test_instance_list_elaborated_def] >>
      qexistsl [`[]`,`Entailment [] [] («Foldable»,UserType 0)`] >>
      simp[has_dicts_empty,specialises_inst_def,subst_db_def,MEM_MAP]
    ) >>
    irule has_dict_lie >>
    simp[]
  )
  >- (
    simp[Once test_class_map_def,type_elaborate_impls_def,
        type_elaborate_impl_def] >>
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
    simp[Once test_class_map_def,type_elaborate_impls_def,
        type_elaborate_impl_def] >>
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
    simp[Once test_class_map_def,type_elaborate_impls_def,
        type_elaborate_impl_def] >>
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
    simp[has_dicts_simp,test_class_map_def,
      class_map_to_env_def,specialises_pred_def,
      subst_db_pred_def,subst_db_Functions,
      subst_db_def,get_method_type_def,PULL_EXISTS] >>
    simp[kind_ok_def,LLOOKUP_THM] >>
    rpt (irule_at Any has_dict_lie) >>
    simp[shift_db_pred_def,shift_db_def,subst_db_pred_def,subst_db_def]
  )
  >- (
    simp[Once test_class_map_def,type_elaborate_impls_def,
        type_elaborate_impl_def] >>
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
    simp[class_map_to_env_def,test_class_map_def,get_method_type_def,
      has_dicts_simp] >>
    simp[specialises_pred_def,subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def,PULL_EXISTS,
      subst_db_def,shift_db_def] >>
    rpt (irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL) >>
    simp[kind_ok_def,LLOOKUP_THM] >>
    rpt (irule_at Any has_dict_lie) >>
    simp[] >>
    irule_at Any exhaustive_cepat_Cons >>
    simp[PULL_EXISTS,unsafe_destruct_type_cons_def,
      split_ty_cons_def,split_ty_cons_aux_def,
      destructable_type_def,head_ty_cons_def] >>
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
      (Pat `exhaustive_cepat _ _ {cepatCons «» [_;_]}`)
      exhaustive_cepat_Cons >>
    simp[PULL_EXISTS,unsafe_destruct_type_cons_def,head_ty_cons_def,
      split_ty_cons_def,split_ty_cons_aux_def,destructable_type_def] >>
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
  ie = set (MAP SND (class_map_to_ie test_class_map)) ∪
    set (MAP SND
      (instance_list_to_ie test_instance_list_elaborated)) ∧
  env = [
    «test»,[],PredType [] $
      Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
        (Atom $ PrimTy Integer);
    «append»,[kindType],PredType [] $
      Functions [
        Cons (UserType 0) (TypeVar 0);
        Cons (UserType 0) (TypeVar 0)] $
        Cons (UserType 0) (TypeVar 0)] ++
    class_map_to_env test_class_map ⇒

  type_elaborate_default_impls test_class_map initial_namespace
    ie st env test_defaults test_defaults_elaborated test_defaults_types
Proof
  rw[test_defaults_def,test_defaults_elaborated_def,
    type_elaborate_default_impls_def,test_defaults_types_def] >>
  simp[Once test_class_map_def,LIST_REL3_simp,PULL_EXISTS] >>
  qexists `«Foldable»` >>
  simp[type_elaborate_default_impl_def,get_method_type_def] >>
  irule type_elaborate_texp_Pred >>
  simp[pred_type_well_scoped_def,pred_type_kind_ok_def,
    pred_kind_wf_def,collect_type_vars_def,Once Functions_def] >>
  simp[Once Functions_def,LLOOKUP_THM] >>
  simp[Once Functions_def,LLOOKUP_THM,
    Once typedefs_to_cdb_def,Once initial_namespace_def] >>
  simp[Once initial_namespace_def,Once test_class_map_def,
    kind_arrows_def,class_map_to_clk_def] >>
  irule type_elaborate_texp_App >>
  simp[LIST_REL3_simp,PULL_EXISTS,GSYM Functions_APPEND] >>
  irule_at (Pos last) type_elaborate_texp_Var >>
  simp[Once class_map_to_env_def,Once test_class_map_def,
    get_method_type_def,has_dicts_simp,LIST_REL3_simp,
    PULL_EXISTS,specialises_pred_def,subst_db_pred_def,kind_ok_def,
    subst_db_Functions,subst_db_def,shift_db_pred_def,shift_db_def,
    shift_db_Functions] >>
  irule_at (Pos last) type_elaborate_texp_Lam >>
  irule_at (Pat `type_elaborate_texp`) type_elaborate_texp_Cons >>
  simp[LIST_REL3_simp,PULL_EXISTS] >>
  irule_at (Pat `type_elaborate_texp`) type_elaborate_texp_Var >>
  simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
    subst_db_def,shift_db_def,shift_db_pred_def] >>
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
  qexists `Entailment [kindType] [] («Monoid»,Cons (UserType 0) (TypeVar 0))`>>
  simp[instance_list_to_ie_def,instance_to_entailment_def,has_dicts_simp,
    test_instance_list_elaborated_def,PULL_EXISTS,kind_ok_def,
    specialises_inst_def,subst_db_def,LLOOKUP_THM]
QED

Theorem test_prog_type_check:
  type_elaborate_prog initial_namespace st test_class_map
    test_defaults test_instance_list test_prog (Var [] «test»)
    (Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
        (Atom $ PrimTy Integer))
    test_defaults_elaborated test_instance_list_elaborated
    test_prog_elaborated (Var [] «test»)
Proof
  simp[type_elaborate_prog_def,
    FRANGE_alist_to_fmap_class_map_instance_list] >>
  irule_at Any test_instance_list_type_check >>
  irule_at Any test_defaults_type_check >>
  simp[test_prog_elaborated_def,test_prog_def] >>
  rw[]
  >>~- ([`pred_type_kind_ok`],
    simp[pred_type_kind_ok_def,typedefs_to_cdb_def,kind_arrows_def,
      pred_kind_wf_def,Functions_def,LLOOKUP_THM,
      initial_namespace_def]
  )
  >~ [`class_map_kind_ok`]
  >- (
    rw[class_map_kind_ok_def,test_class_map_def,
      class_map_to_clk_def] >>
    simp[super_classes_def,pred_type_kind_ok_def,
      typedefs_to_cdb_def,kind_arrows_def,
      pred_kind_wf_def,Functions_def,LLOOKUP_THM,
      initial_namespace_def]
  )
  >~ [`instance_list_kind_ok`]
  >- (
    simp[instance_list_kind_ok_def,instance_kind_ok_def,
      entailment_kind_ok_def,instance_to_entailment_def,
      test_instance_list_elaborated_def,kind_ok_def,LLOOKUP_THM,
      kind_arrows_def,typedefs_to_cdb_def,initial_namespace_def] >>
    EVAL_TAC
  )
  >>~- ([`¬MEM _ (method_names _)`],
    simp[test_class_map_def,method_names_def,MEM_MAP,class_map_to_env_def,
      FORALL_PROD]
  )
  >>~ [`ALL_DISTINCT`]
  >>~- ([`ALL_DISTINCT`],
    simp[test_defaults_def,method_names_def,test_class_map_def])
  >>~- ([`set (MAP _ _) ⊆ set (method_names _)`],
    simp[method_names_def,test_class_map_def,class_map_to_env_def,
      test_defaults_def]
  ) >>
  irule type_elaborate_texp_Letrec >>
  conj_tac >- simp[] >>
  irule_at Any type_elaborate_texp_Var >>
  simp[has_dicts_empty,LIST_REL3_simp] >>
  simp[PULL_EXISTS,EXISTS_PROD,specialises_pred_def,
    subst_db_pred_def,shift_db_pred_def] >>
  conj_tac
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
    >- rw[destructable_type_def,initial_namespace_def,head_ty_cons_def]
    >- (
      gvs[initial_namespace_def,unsafe_destruct_type_cons_def,
        split_ty_cons_def,split_ty_cons_aux_def,unsafe_type_cons_def,
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
    )
    >- (
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
    irule_at Any type_elaborate_texp_Var >>
    simp[specialises_pred_def,subst_db_pred_def,
      has_dicts_simp]
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
    >- simp[Functions_def,LLOOKUP_THM,class_map_to_clk_def,test_class_map_def]
    >- simp[Functions_def,LLOOKUP_THM,class_map_to_clk_def,test_class_map_def] >>
    irule type_elaborate_texp_App >>
    simp[LIST_REL3_simp,PULL_EXISTS,GSYM Functions_APPEND] >>
    irule_at Any type_elaborate_texp_Var >>
    simp[Once class_map_to_env_def,Once test_class_map_def,
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
    qexistsl [`[]`,`Entailment [] [] («Foldable»,UserType 0)`] >>
    simp[instance_list_to_ie_def,test_instance_list_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,
      specialises_inst_def]
  ) >>
  `∀(ns:typedefs) db lie. has_dict ns db
    (set (MAP SND $ class_map_to_ie test_class_map) ∪
     set (MAP SND $
       instance_list_to_ie test_instance_list_elaborated)) lie
    («Monoid»,Atom (PrimTy Integer))`
  by (
    rpt strip_tac >>
    irule has_dict_ie >>
    qexistsl [`[]`,`Entailment [] [] («Monoid»,Atom (PrimTy Integer))`] >>
    simp[instance_list_to_ie_def,test_instance_list_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,
      specialises_inst_def]
  ) >>
  conj_asm1_tac
  >- (
    irule has_dict_ie >>
    CONV_TAC $ RESORT_EXISTS_CONV rev >>
    qexists `Entailment [kindType; kindType]
         [(«Monoid»,TypeVar 0); («Monoid»,TypeVar 1)]
         («Monoid»,Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1))` >>
    simp[Once instance_list_to_ie_def,
      Once test_instance_list_elaborated_def,
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
    qexistsl [`[]`,`Entailment [kindType] [] («Monoid»,Cons (UserType 0) (TypeVar 0))`] >>
    simp[instance_list_to_ie_def,test_instance_list_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,subst_db_def,
      specialises_inst_def,PULL_EXISTS,kind_ok_def,
      kind_arrows_def]
  ) >>
  simp[Once class_map_to_env_def,Once test_class_map_def,
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

Theorem test_cl_cons:
  class_dict_constructor_names test_class_map = [
    «SemigroupDict»;
    «MonoidDict»;
    «FoldableDict»
  ]
Proof
  simp[class_dict_constructor_names_def,test_class_map_def]
QED

Theorem test_sup_vs:
  super_class_accessor_names test_class_map =
   [«getSemigroup»]
Proof
  simp[super_class_accessor_names_def,test_class_map_def]
QED

Theorem test_inst_vs:
  instance_dict_names test_instance_list_elaborated = [
    «semigroupInt»;
    «monoidInt»;
    «foldableList»;
    «semigroupList»;
    «monoidList»;
    «monoidTuple»;
    «semigroupTuple»
  ]
Proof
  simp[instance_dict_names_def,
    test_instance_list_elaborated_def]
QED

Theorem test_default_vs:
  default_method_names test_defaults_elaborated = [«default_toList»]
Proof
  simp[default_method_names_def,test_defaults_elaborated_def]
QED

Theorem test_method_vs =
  EVAL ``method_names test_class_map``;

Definition test_cl_to_tyid_def:
  test_cl_to_tyid =
    to_cl_tyid_map (SND initial_namespace) test_class_map
End

Theorem test_cl_to_tyid = EVAL ``test_cl_to_tyid``;

Definition test_methods_translated_def:
  test_methods_translated =
    class_map_construct_methods test_class_map
End

Theorem test_methods_translated =
  EVAL ``test_methods_translated``;

Definition test_supers_translated_def:
  test_supers_translated =
    class_map_construct_super_accessors test_class_map
End

Theorem test_supers_translated =
  EVAL ``test_supers_translated``;

Definition test_ie_def:
  test_ie = FEMPTY |++
     (class_map_to_ie test_class_map ++
      instance_list_to_ie test_instance_list_elaborated)
End

Theorem test_ie = EVAL ``test_ie``;

Definition test_env_def:
  test_env =
    set (MAP (FST ∘ FST) test_prog_elaborated) ∪
         set (method_names test_class_map)
End

Theorem test_class_map_to_env =
  EVAL ``class_map_to_env test_class_map``;

Theorem test_env:
  test_env =
    {«append»; «test»; «mappend»; «mempty»; «foldMap»; «toList»}
Proof
  simp[test_env_def,method_names_def,test_class_map_def,
    test_prog_elaborated_def] >>
  EVAL_TAC
QED

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
  default_impls_construct_dict initial_namespace test_class_map
    test_ie test_env test_defaults_elaborated test_defaults_translated
Proof
  simp[default_impls_construct_dict_def] >>
  simp[test_defaults_elaborated_def,test_defaults_translated_def] >>
  qexists `«Foldable»` >>
  simp[Once test_class_map_def] >>
  simp[default_impl_construct_dict_def,get_method_type_def] >>
  irule texp_construct_dict_Pred >>
  simp[LENGTH_EQ_NUM_compute,PULL_EXISTS] >>
  simp[test_ie,test_env,get_names_namespace_def,
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
  simp[construct_dicts_simp,test_ie,finite_mapTheory.FLOOKUP_SIMP] >>
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

Definition test_instance_list_translated_def:
  test_instance_list_translated = [
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

Theorem test_instance_list_construct_dict:
  instance_list_construct_dict initial_namespace test_class_map
    test_ie test_env test_defaults_elaborated
    test_instance_list_elaborated test_instance_list_translated
Proof
  simp[instance_list_construct_dict_def,LIST_REL3_def,
    instance_construct_dict_def,test_instance_list_elaborated_def,
    test_instance_list_translated_def] >>
  rw[] >>
  simp[Once test_class_map_def,PULL_EXISTS,construct_dicts_simp,
    super_classes_def]
  >- (
    simp[impl_construct_dict_def,impl_construct_dict_instantiated_def,
      subst_db_pred_def,shift_db_pred_def,shift_db_def,subst_db_def,
      shift_db_Functions,subst_db_Functions] >>
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
    conj_tac >- (
      irule construct_dict_ie >>
      simp[test_ie,finite_mapTheory.FLOOKUP_SIMP] >>
      simp[specialises_inst_def,subst_db_def,construct_dicts_simp]
    ) >>
    simp[impl_construct_dict_def,impl_construct_dict_instantiated_def,
      subst_db_pred_def,shift_db_pred_def,shift_db_def,subst_db_def,
      shift_db_Functions,subst_db_Functions] >>
    irule texp_construct_dict_Pred >>
    simp[SmartLam_def] >>
    irule texp_construct_dict_Prim >> simp[]
  )
  >- (
    simp[impl_construct_dict_def,impl_construct_dict_instantiated_def,
      subst_db_pred_def,shift_db_pred_def,shift_db_def,subst_db_def,
      shift_db_Functions,subst_db_Functions] >>
    simp[SmartLam_def,test_defaults_elaborated_def] >>
    irule texp_construct_dict_Pred >>
    simp[SmartLam_EQ_Lam_cases,LENGTH_EQ_NUM_compute,PULL_EXISTS] >>
    conj_tac
    >-  (
      simp[test_ie,test_env,lambda_vars_def,
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
      simp[Once test_ie,finite_mapTheory.FLOOKUP_UPDATE] >>
      simp[specialises_inst_def,PULL_EXISTS,kind_ok_def,subst_db_def] >>
      simp[LAMBDA_PROD,GSYM PEXISTS_THM,LLOOKUP_THM,construct_dicts_simp]
    ) >>
    irule construct_dict_ie >>
    simp[Once test_ie,finite_mapTheory.FLOOKUP_UPDATE] >>
    simp[specialises_inst_def,subst_db_def,construct_dicts_simp]
  )
  >- (
    simp[impl_construct_dict_def,impl_construct_dict_instantiated_def,
      subst_db_pred_def,shift_db_pred_def,shift_db_def,subst_db_def,
      shift_db_Functions,subst_db_Functions,SmartLam_def] >>
    irule texp_construct_dict_Pred >>
    simp[] >>
    irule texp_construct_dict_Var >>
    simp[construct_dicts_simp]
  )
  >- (
    conj_tac >- (
      irule construct_dict_ie >>
      simp[Once test_ie,finite_mapTheory.FLOOKUP_UPDATE] >>
      simp[specialises_inst_def,subst_db_def,PULL_EXISTS,kind_ok_def,
        LLOOKUP_THM,construct_dicts_simp]
    ) >>
    simp[impl_construct_dict_def,impl_construct_dict_instantiated_def,
      subst_db_pred_def,shift_db_pred_def,shift_db_def,subst_db_def,
      shift_db_Functions,subst_db_Functions,SmartLam_def] >>
    irule texp_construct_dict_Pred >>
    simp[] >>
    irule texp_construct_dict_Prim >>
    simp[]
  )
  >- (
    rw[SmartLam_EQ_Lam_cases,LENGTH_EQ_NUM_compute,PULL_EXISTS]
    >>~- ([`_ ∉ _`], simp[test_env,test_ie])
    >- (
      irule construct_dict_ie >>
      simp[Once test_ie,finite_mapTheory.FLOOKUP_SIMP] >>
      simp[specialises_inst_def,subst_db_def,PULL_EXISTS,
        kind_ok_def,LLOOKUP_THM,construct_dicts_simp] >>
      simp[LAMBDA_PROD,GSYM PEXISTS_THM] >>
      rpt (irule_at Any construct_dict_ie) >>
      simp[] >>
      qpat_abbrev_tac `getSemigroupIt = FLOOKUP test_ie _` >>
      pop_assum $ mp_tac o
        SRULE[markerTheory.Abbrev_def,test_ie,
          finite_mapTheory.FLOOKUP_UPDATE] >>
      disch_then SUBST_ALL_TAC >>
      simp[specialises_inst_def,PULL_EXISTS,subst_db_def,
        kind_ok_def,LLOOKUP_THM] >>
      simp[LAMBDA_PROD,GSYM PEXISTS_THM,construct_dicts_simp] >>
      rpt (irule_at Any construct_dict_lie) >>
      simp[alistTheory.FLOOKUP_FUPDATE_LIST]
    ) >>
    simp[impl_construct_dict_def,impl_construct_dict_instantiated_def,
      subst_db_pred_def,shift_db_pred_def,shift_db_def,subst_db_def,
      shift_db_Functions,subst_db_Functions] >>
    simp[SmartLam_def,dest_Lam_def] >>
    irule texp_construct_dict_Pred >>
    simp[LENGTH_EQ_NUM_compute,PULL_EXISTS] >>
    simp[SmartLam_EQ_Lam_cases] >>
    conj_tac
    >- (
      simp[test_ie,test_env,lambda_vars_def,
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
    impl_construct_dict_instantiated_def,
    subst_db_pred_def,shift_db_pred_def,shift_db_def,subst_db_def,
    shift_db_Functions,subst_db_Functions] >>
  rw[SmartLam_def,dest_Lam_def]
  >>~- ([`_ ∉ _`], simp[test_env,test_ie]) >>
  irule texp_construct_dict_Pred >>
  simp[SmartLam_EQ_Lam_cases,LENGTH_EQ_NUM_compute,PULL_EXISTS] >>
  conj_tac
  >- (
    simp[test_ie,test_env,lambda_vars_def,
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

Theorem test_prog_vs = EVAL ``MAP (FST ∘ FST) test_prog_elaborated``;

Theorem test_prog_lambda_varsl = (EVAL THENC SCONV[] THENC EVAL) $
  ``lambda_varsl (MAP SND test_prog_elaborated)``;

Theorem test_defaults_lambda_varsl = (EVAL THENC SCONV[] THENC EVAL) $
  ``lambda_varsl (MAP (SND ∘ SND) test_defaults_elaborated)``;

Theorem test_instance_list_lambda_varsl =
  (EVAL THENC SCONV[] THENC EVAL) $
  ``lambda_varsl $
    MAP SND (LIST_BIND test_instance_list_elaborated (λx. x.impls))``;

Theorem test_prog_construct_dict:
  prog_construct_dict initial_namespace
    test_class_map test_defaults_elaborated
    test_instance_list_elaborated test_prog_elaborated
    (Var [] «test»)
    (Letrec ()
      (test_defaults_translated ++
        test_supers_translated ++
        test_instance_list_translated ++
        test_methods_translated ++ test_prog_translated)
      (Var () «test»))
Proof
  simp[prog_construct_dict_def] >>
  simp[GSYM test_ie_def,GSYM $ SRULE[] test_env_def,
    GSYM test_methods_translated_def,
    GSYM test_supers_translated_def] >>
  irule_at Any test_defaults_construct_dict >>
  irule_at Any test_instance_list_construct_dict >>
  rw[test_cl_cons,test_sup_vs,test_inst_vs,test_default_vs,
    test_method_vs,test_prog_vs,test_prog_lambda_varsl,
    test_defaults_lambda_varsl,test_instance_list_lambda_varsl] >>
  irule texp_construct_dict_Letrec >>
  rw[test_prog_translated_def,test_prog_elaborated_def]
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
  )
  >- (
    irule texp_construct_dict_Pred >>
    simp[] >>
    irule texp_construct_dict_Letrec >>
    rw[]
    >- (
      irule texp_construct_dict_Pred >>
      simp[SmartLam_EQ_Lam_cases,LENGTH_EQ_NUM_compute,PULL_EXISTS] >>
      conj_tac >- (
        simp[get_names_namespace_def,initial_namespace_def,
          lambda_vars_def,test_class_map_to_env,test_ie,shift_db_def,
          finite_mapTheory.FUPDATE_LIST_THM,
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
    simp[test_ie,construct_dicts_simp,
        finite_mapTheory.FLOOKUP_UPDATE,subst_db_def,PULL_EXISTS,
        specialises_inst_def,kind_ok_def,kind_arrows_def] >>
    simp[LAMBDA_PROD,GSYM PEXISTS_THM] >>
    irule construct_dict_ie >>
    simp[finite_mapTheory.FLOOKUP_UPDATE,construct_dicts_simp,
      specialises_inst_def,subst_db_def,PULL_EXISTS]
  ) >>
  irule texp_construct_dict_Var >>
  simp[construct_dicts_simp]
QED

val _ = export_theory();
