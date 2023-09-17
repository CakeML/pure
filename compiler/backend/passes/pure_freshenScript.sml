(*
   Freshening of bound variables.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite monadsyntax;
open pairTheory listTheory rich_listTheory pred_setTheory
open pure_cexpTheory pure_varsTheory var_setTheory;

val _ = new_theory "pure_freshen";

(***** State monad *****)

(* State: var_set (set of names to avoid), num (max variable name length) *)
Type freshenM[pp] = ``:(var_set # num) -> ('a # (var_set # num))``

Definition freshen_return_def:
  freshen_return x : 'a freshenM = λs. (x, s)
End

Definition freshen_bind_def:
  freshen_bind (g :'a freshenM) (f : 'a -> 'b freshenM) : 'b freshenM = UNCURRY f o g
End

Definition freshen_ignore_bind_def:
  freshen_ignore_bind g f = freshen_bind g (λx. f)
End

val freshen_monadinfo : monadinfo = {
  bind = “freshen_bind”,
  ignorebind = SOME “freshen_ignore_bind”,
  unit = “freshen_return”,
  fail = NONE,
  choice = NONE,
  guard = NONE
  };

val _ = declare_monad ("freshen", freshen_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "freshen";

Overload return[local] = ``freshen_return``;

Definition freshen_mfoldl_def:
  freshen_mfoldl f acc [] = return acc ∧
  freshen_mfoldl f acc (x::xs) = do
    acc' <- f acc x;
    freshen_mfoldl f acc' xs
  od
End

Theorem freshen_mfoldl_cong[defncong]:
  ∀l l' acc acc' f f'.
    l = l' ∧ acc = acc' ∧
    (∀x a. MEM x l' ⇒ f a x = f' a x)
  ⇒ freshen_mfoldl f acc l = freshen_mfoldl f' acc' l'
Proof
  Induct >> rw[] >> gvs[freshen_mfoldl_def] >>
  AP_TERM_TAC >> rw[FUN_EQ_THM]
QED

(***** Implementation *****)

Definition fresh_def:
  fresh (v : mlstring) (avoid : var_set) =
    if cmp_of avoid = var_cmp then
      case lookup avoid v of
      | NONE => v
      | SOME () => fresh (strcat v «'») avoid
    else v
Termination
  WF_REL_TAC `measure (λ(v,avoid).
    (MAX_SET $ IMAGE strlen {v | lookup avoid v ≠ NONE}) + 1 - strlen v)` >>
  rw[] >>
  `FINITE {v | lookup avoid v ≠ NONE}` by (
    pop_assum kall_tac >>
    Cases_on `avoid` >> gvs[mlmapTheory.lookup_def, mlmapTheory.cmp_of_def] >>
    Induct_on `b` >> rw[] >> gvs[balanced_mapTheory.lookup_def] >>
    qmatch_goalsub_abbrev_tac `FINITE s` >>
    `s = {v | lookup var_cmp v b ≠ NONE ∧ var_cmp v k = Less} ∪
         {v | var_cmp v k = Equal} ∪
         {v | lookup var_cmp v b' ≠ NONE ∧ var_cmp v k = Greater}` by (
      unabbrev_all_tac >> rw[EXTENSION] >>
      CASE_TAC >> gvs[]) >>
    gvs[] >> pop_assum kall_tac >> rw[]
    >- (irule SUBSET_FINITE >> goal_assum rev_drule >> rw[SUBSET_DEF])
    >- (
      rw[var_cmp_def] >>
      assume_tac mlstringTheory.TotOrd_compare >> gvs[totoTheory.TotOrd]
      )
    >- (irule SUBSET_FINITE >> goal_assum drule >> rw[SUBSET_DEF])
    ) >>
  `v ∈ {v | lookup avoid v ≠ NONE}` by gvs[] >>
  qmatch_asmsub_abbrev_tac `FINITE s` >> pop_assum kall_tac >>
  qsuff_tac `strlen v ≤ MAX_SET (IMAGE strlen s)` >> rw[] >>
  qspec_then `IMAGE strlen s` mp_tac X_LE_MAX_SET >> simp[PULL_EXISTS]
End


(* Generate a single fresh variable, adding it to both avoid and renaming sets *)
Definition fresh_boundvar_def:
  fresh_boundvar v varmap = do
    v' <- invent_var v;
    return (v', if v = v' then varmap else insert varmap v v')
    od
End

(* Generate several fresh variables, adding to both avoid and renaming sets.
   If there is shadowing, the last renaming will be kept. *)
Definition fresh_boundvars_def:
  fresh_boundvars [] varmap = return ([], varmap) ∧
  fresh_boundvars (v::vs) varmap = do
    (v', varmap') <- fresh_boundvar v varmap;
    (vs', varmap'') <- fresh_boundvars vs varmap';
    return (v'::vs', varmap'')
  od
End

(*
  freshen_aux :
       (varmap : mlstring var_map)  -- variable renamings generated higher in the AST
    -> 'a cexp                      -- expression
    -> (avoid : var_set)            -- variable names to avoid
    -> ('a cexp, var_set)           -- new expression and new avoid set

  `avoid` is *global*, i.e. for `App e1 [e2]` variables used in `e1` will not
  be used in `e2`.  However, `varmap` is *scoped*, i.e. mappings in `e1` are
  not used in `e2` and descending under `Lam x` will overwrite any `x` bindings
  in `varmap`.  The resulting "avoid set" will contain the old avoid set and
  all fresh variable names created.  The initial avoid set must contain all
  free variables of the expression.
*)
Definition freshen_aux_def:
  freshen_aux varmap (Var d v) = do
    v' <<- (case lookup varmap v of | NONE => v | SOME v' => v');
    return $ Var d v'
  od ∧

  freshen_aux varmap (Prim d cop ces) = do
    ces' <- freshen_aux_list varmap ces;
    return $ Prim d cop ces'
  od ∧

  freshen_aux varmap (App d ce ces) = do
    ce' <- freshen_aux varmap ce;
    ces' <- freshen_aux_list varmap ces;
    return $ App d ce' ces'
  od ∧

  freshen_aux varmap (Lam d vs ce) = do
    (vs', varmap') <- fresh_boundvars vs varmap;
    ce' <- freshen_aux varmap' ce;
    return $ Lam d vs' ce'
  od ∧

  freshen_aux varmap (Let d v ce1 ce2) = do
    ce1' <- freshen_aux varmap ce1;
    (v',varmap') <- fresh_boundvar v varmap;
    ce2' <- freshen_aux varmap' ce2;
    return $ Let d v' ce1' ce2'
  od ∧

  freshen_aux varmap (Letrec d fns ce) = do
    (fs', varmap') <- fresh_boundvars (MAP FST fns) varmap;
    fces' <- freshen_mfoldl (λacc (f,fce). do
                fce' <- freshen_aux varmap' fce;
                return $ fce'::acc od)
              [] fns;
    ce' <- freshen_aux varmap' ce;
    return $ Letrec d (ZIP (fs', REVERSE fces')) ce'
  od ∧

  freshen_aux varmap (Case d ce v css usopt) = do
    ce' <- freshen_aux varmap ce;
    (v',varmap') <- fresh_boundvar v varmap;
    css' <- freshen_mfoldl (λacc (cn,pvs,ce). do
                (pvs',varmap'') <- fresh_boundvars pvs varmap';
                ce' <- freshen_aux varmap'' ce;
                return $ (cn,pvs',ce')::acc od)
              [] css;
    usopt' <- (case usopt of
              | NONE => return NONE
              | SOME (cn_ars, usce) => do
                 usce' <- freshen_aux varmap' usce;
                 return $ SOME (cn_ars, usce') od);
    return (Case d ce' v' (REVERSE css') usopt')
  od ∧

  freshen_aux _ ce = return ce ∧ (* NestedCase not handled *)

  (* List form *)
  freshen_aux_list varmap [] = return [] ∧
  freshen_aux_list varmap (ce::ces) = do
    ce' <- freshen_aux varmap ce;
    ces' <- freshen_aux_list varmap ces;
    return $ ce'::ces'
  od
Termination
  WF_REL_TAC `measure $ λx. case x of
    | INL (_, ce) => cexp_size (K 0) ce
    | INR (_, ces) => list_size (cexp_size $ K 0) ces`
End

Definition freshen_cexp_def:
  freshen_cexp = freshen_aux empty
End

(**********)

Definition boundvars_of_def:
  boundvars_of (Var c x) = empty_vars ∧
  boundvars_of (Prim c cop ces) =
   FOLDR (λce s. var_union s $ boundvars_of ce) empty_vars ces ∧
  boundvars_of (App c ce ces) =
   FOLDR (λce s. var_union s $ boundvars_of ce) (boundvars_of ce) ces ∧
  boundvars_of (Lam c xs ce) = insert_vars (boundvars_of ce) xs ∧
  boundvars_of (Let c x ce1 ce2) =
    insert_var (var_union (boundvars_of ce1) (boundvars_of ce2)) x ∧
  boundvars_of (Letrec c fns ce) =
    FOLDR (λ(f,body) s. var_union s $ insert_var (boundvars_of body) f)
      (boundvars_of ce) fns ∧
  boundvars_of (Case c ce x css us) =
    var_union (insert_var (boundvars_of ce) x) $
    var_union (case us of NONE => empty_vars | SOME (_,ce) => boundvars_of ce) $
    FOLDR (λ(cn,vs,ce) s. var_union s $ insert_vars (boundvars_of ce) vs)
      empty_vars css ∧
  boundvars_of (NestedCase c ce x p pce pces) =
    var_union (insert_var (boundvars_of ce) x) $
    var_union (insert_vars (boundvars_of pce) (cepat_vars_l p)) $
    FOLDR (λ(p,ce) s. var_union s $ insert_vars (boundvars_of ce) (cepat_vars_l p))
      empty_vars pces
Termination
  WF_REL_TAC `measure $ cexp_size (K 0)`
End

val _ = export_theory();
