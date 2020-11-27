
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory configTheory pairTheory listTheory finite_mapTheory;

val _ = new_theory "exp";

(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)
Type fname = “:string”  (* function name *)

Datatype:
  op = If                 (* if-expression                            *)
     | Cons string        (* datatype constructor                     *)
     | IsEq string num    (* compare cons tag and num of args         *)
     | Proj string num    (* reading a field of a constructor         *)
     | AtomOp atom_op     (* primitive parametric operator over Atoms *)
     | Lit lit            (* parametric literal Atom                  *)
End

Datatype:
  exp = Var vname                     (* variable                   *)
      | Prim op (exp list)            (* primitive operations       *)
      | App exp exp                   (* function application       *)
      | Lam vname exp                 (* lambda                     *)
      | Letrec ((fname # vname # exp) list) exp   (* mut. rec. funs *)
      | Case exp vname ((vname # vname list # exp) list) (*case pat.*)
End

(* some abbreviations *)
Overload Let  = “λs x y. App (Lam s y) x”      (* let-expression    *)
Overload If   = “λx y z. Prim If [x; y; z]”    (* If   at exp level *)
Overload Lit  = “λa. Prim (Lit a) []”           (* Lit at exp level *)
Overload Cons = “λs. Prim (Cons s)”            (* Cons at exp level *)
Overload IsEq = “λs n x. Prim (IsEq s n) [x]”  (* IsEq at exp level *)
Overload Proj = “λs i x. Prim (Proj s i) [x]”  (* Proj at exp level *)
Overload Fail = “Prim (Lit ARB) [Prim (Lit ARB)[]]” (* causes Error *)

Definition freevars_def[simp]:
  freevars (Var n)     = [n]                               ∧
  freevars (Prim _ es) = (FLAT (MAP freevars es))          ∧
  freevars (App e1 e2) = (freevars e1 ⧺ freevars e2)       ∧
  freevars (Lam n e)   = (FILTER ($≠ n) (freevars e))      ∧
  freevars (Letrec lcs e) =
    FILTER (\n. ¬ MEM n (MAP FST lcs))
           (freevars e ⧺
            FLAT (MAP (λ(fn,vn,e). FILTER (λ n.n ≠ vn) (freevars e)) lcs))  ∧
  freevars (Case exp nm css) =
    (freevars exp ⧺ FLAT (MAP (λ(_,vs,cs).FILTER (λ n. ¬MEM n (nm::vs)) (freevars cs))
                              css))
Termination
  WF_REL_TAC ‘measure exp_size’ \\ fs[]
  \\ conj_tac \\ TRY conj_tac
  \\ TRY (Induct_on ‘lcs’)
  \\ TRY (Induct_on ‘css’)
  \\ TRY (Induct_on ‘es’)
  \\ rw [] \\ fs [fetch "-" "exp_size_def"] \\ res_tac \\ fs[]
  \\ pop_assum (assume_tac o SPEC_ALL) \\ fs[]
End

Overload freevars = “λe. set (freevars e)”;

Definition closed_def:
  closed e = (freevars e = [])
End

Theorem exp_size_lemma:
  (∀xs     a. MEM      a  xs ⇒ exp_size a < exp7_size xs) ∧
  (∀xs x y a. MEM (x,y,a) xs ⇒ exp_size a < exp3_size xs) ∧
  (∀xs x y a. MEM (x,y,a) xs ⇒ exp_size a < exp1_size xs)
Proof
  conj_tac \\ TRY conj_tac \\ Induct \\ rw []
  \\ res_tac \\ fs [fetch "-" "exp_size_def"]
QED

Definition subst_def:
  subst name v (Var s) = (if name = s then v else Var s) ∧
  subst name v (Prim op xs) = Prim op (MAP (subst name v) xs) ∧
  subst name v (App x y) = App (subst name v x) (subst name v y) ∧
  subst name v (Lam s x) = Lam s (if s = name then x else subst name v x) ∧
  subst name v (Letrec f x) =
    (if MEM name (MAP FST f) then Letrec f x else
      Letrec (MAP (λ(g,m,z). (g,m, if name = m then z else subst name v z )) f)
             (subst name v x)) ∧
  subst name v (Case e vn css) =
    (Case (subst name v e)
          vn
          (MAP (λ(cn,ans, cb).
                 (cn,ans, if ¬MEM name (vn::ans) then subst name v cb else cb))
               css))
Termination
  WF_REL_TAC `measure (λ(n,v,x). exp_size x)` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

Definition subst_all_def:
  subst_all m (Var s) =
    (case FLOOKUP m s of
     | NONE => Var s
     | SOME x => x) ∧
  subst_all m (Prim op xs) = Prim op (MAP (subst_all m) xs) ∧
  subst_all m (App x y) = App (subst_all m x) (subst_all m y) ∧
  subst_all m (Lam s x) = Lam s (subst_all (m \\ s) x) ∧
  subst_all m (Letrec f x) =
    (let m1 = FDIFF m (set (MAP FST f)) in
       Letrec
         (MAP (λ(f,x,e). (f,x,subst_all (m1 \\ x) e)) f)
         (subst_all m1 x)) ∧
  subst_all m (Case e vn rows) =
    let m1 = m \\ vn in
      Case (subst_all m e) vn
          (MAP (λ(cn,ps,e).
                 (cn,ps,subst_all (FDIFF m1 (set ps)) e)) rows)
Termination
  WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

Definition bind_all_def:
  bind_all m e =
    if (∀n v. FLOOKUP m n = SOME v ⇒ closed v) then subst_all m e else Fail
End

Overload bind = “bind_all”;

Theorem subst_ignore:
  ∀s x y. ~MEM s (freevars y) ⇒ subst s x y = y
Proof
  ho_match_mp_tac subst_ind \\ rw [] \\ fs [subst_def]
  THEN1 (Induct_on ‘xs’ \\ fs [])
  THEN1 (rw [] \\ fs [MEM_FILTER])
  THEN1
   (rw [] \\ fs [MEM_FILTER]
    \\ Induct_on ‘f’ \\ fs [FORALL_PROD]
    \\ rw [] \\ fs [AND_IMP_INTRO]
    THEN1 (first_x_assum match_mp_tac \\ metis_tac [])
    \\ fs [MEM_FILTER,EXISTS_PROD,MEM_MAP]
    \\ metis_tac [])
  \\ Induct_on ‘css’ \\ fs [FORALL_PROD,MEM_MAP] \\ rw []
  \\ fs [MEM_FILTER,EXISTS_PROD,MEM_MAP]
  \\ metis_tac []
QED

Theorem closed_subst[simp]:
  ∀s x y. closed y ⇒ subst s x y = y
Proof
  rw [] \\ match_mp_tac subst_ignore \\ fs [closed_def]
QED

Theorem subst_subst:
  ∀x1 v1 e x2 v2.
    x1 ≠ x2 ∧ closed v1 ∧ closed v2 ⇒
    subst x1 v1 (subst x2 v2 e) = subst x2 v2 (subst x1 v1 e)
Proof
  ho_match_mp_tac subst_ind \\ rw [] \\ rw [subst_def] \\ gvs []
  THEN1 (Induct_on ‘xs’ \\ fs [] \\ metis_tac [])
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1
   (IF_CASES_TAC \\ fs []
    \\ fs [MEM_MAP,FORALL_PROD] \\ PairCases_on ‘y’ \\ fs [] \\ gvs [])
  THEN1
   (rpt IF_CASES_TAC \\ fs []
    \\ fs [MEM_MAP,FORALL_PROD] \\ PairCases_on ‘y’ \\ fs [] \\ gvs [])
  THEN1
   (fs [MEM_MAP,FORALL_PROD,EXISTS_PROD]
    \\ reverse conj_tac THEN1 metis_tac []
    \\ Induct_on ‘f’ \\ fs [FORALL_PROD] \\ metis_tac [])
  THEN1 metis_tac []
  \\ Induct_on ‘css’ \\ fs [] \\ rw []
  \\ Cases_on ‘x1 = vn’ \\ fs []
  \\ Cases_on ‘x2 = vn’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs [] \\ rw []
  \\ metis_tac []
QED

val _ = export_theory ();
