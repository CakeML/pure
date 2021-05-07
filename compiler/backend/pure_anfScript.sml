(*
   Defines A-normal-form (ANF) for pure_lang.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     state_transformerTheory ASCIInumbersTheory;


open pure_expTheory pure_exp_lemmasTheory mlmapTheory mlstringTheory
     pure_cexpTheory pure_varsTheory pure_beta_equivTheory;

val _ = new_theory "pure_anf";

(* definition of ANF syntax *)

(*What it should be:
  value  = Var vname
         | Lam (vname list) anf;

  canf   = App value (value list)
         | Prim op (value list)
         | Case vname ((string # vname list # anf) list);

  anf    = Let vname canf anf
         | Letrec ((vname # canf) list) anf
         | canf
         | value;

  this shape reflect the intrinsic property of A-normal form expressions:
  anf expressions are either:
   - values
   - Lambdas/primitives applied to values (App/Prim/Case (If primitive))
   - let binds (Let/Letrec)
*)

(*
  What actually is to avoid mutual recursion:
*)

Datatype:
  anf    = Var 'a vname
         | Lam 'a (vname list) anf
         | App 'a anf (anf list)
         | Prim 'a cop (anf list)
         | Case 'a vname ((string # vname list # anf) list)
         | Let 'a vname anf anf
         | Letrec 'a ((vname # anf) list) anf
End

(*avoiding mutual recursion is a bad idea. The proper datatype
  definition forces the anf expressions to comply with the A-normal
  form intrinsic property (above).
  This relieves us from proving ‘anf_of’ actually produces
  A-normal form expressions (I think).
*)

Definition is_value_def:
    (is_anf_value (Var _ _) = T)
  ∧ (is_anf_value (Lam _ _ _) = T)
  ∧ (is_anf_value _ = F)
End

Definition get_anf_annotation_def:
    get_anf_annotation (Var a _)      = a
  ∧ get_anf_annotation (Lam a _ _)    = a
  ∧ get_anf_annotation (App a _ _)    = a
  ∧ get_anf_annotation (Prim a _ _)   = a
  ∧ get_anf_annotation (Case a _ _)   = a
  ∧ get_anf_annotation (Let a _ _ _)  = a
  ∧ get_anf_annotation (Letrec a _ _) = a
End

Theorem anf_size_lemma:
  (∀ xs n x. MEM (n,x) xs ⇒ anf_size (K 0) x ≤ anf4_size (K 0) xs) ∧
  (∀cases as b. MEM (c,as,b) cases ⇒ anf_size (K 0) b ≤ anf1_size (K 0) cases) ∧
  (∀ xs n x. MEM x xs ⇒ anf_size (K 0) x ≤ anf6_size (K 0) xs)
Proof
  rpt CONJ_TAC
  \\ Induct \\ ntac 2 (rw [fetch "-" "anf_size_def"]) \\ res_tac \\ fs []
QED

(* we use ANF as rigid way of writing normal pure_lang cexp expressions *)

Definition cexp_of_def:
  cexp_of (Var d x) = (Var d x) ∧
  cexp_of (Lam d args b) = Lam d args (cexp_of b) ∧
  cexp_of (App d f args) = App d (cexp_of f) (MAP cexp_of args) ∧
  cexp_of (Prim d cop args) = Prim d cop (MAP cexp_of args) ∧
  cexp_of (Case d v cases) =
       Case d v (MAP (λ(n,as,b).(n,as,cexp_of b)) cases)  ∧
  cexp_of (Let d v a b) = Let d v (cexp_of a) (cexp_of b) ∧
  cexp_of (Letrec d binds body) =
       Letrec d (MAP (λ(v,e).(v,cexp_of e)) binds) (cexp_of body)
Termination
  WF_REL_TAC ‘measure (anf_size (K 0))’ \\ rw []
  \\ imp_res_tac anf_size_lemma \\ fs []
End

val _ = monadsyntax.enable_monadsyntax () ;
monadsyntax.enable_monad "state";


(*state for the normalization algorithm.
  Keeps track of an index used to generate new fresh variables.
*)
Datatype:
  anf_state = <| base        : vname
               ; vname_index : int    |>
End

(*State monad (with state fixed: ‘anf_state’)*)
Type S[local] = “:anf_state -> ('a # anf_state)”;

(*Continuation function type (not a monad)*)
Type CONT[local] = “:('a anf -> ('a anf) S)”;

Definition new_vname_def:
  new_vname : (vname) S = do
          i <- READ (anf_state_vname_index);
          base <- READ (anf_state_base);
          WRITE (λ s. s with vname_index updated_by ($+ 1));
          return (base++toString i);
       od
End

(*takes a continuation k, returns a continuation that
  grabs the returning value (anf_e):
    if is a value (Val or Lam)
      then passes it to k
      else binds it to a fresh variable (t)
           and passes (Var t) to k
*)
Definition let_bind_def:
   let_bind : 'a CONT -> 'a CONT
              k = (λ anf_e.
                     if (is_anf_value anf_e)
                       then k anf_e
                       else (let an_e = get_anf_annotation anf_e in
                               do t <- new_vname ;
                                  anf_res <- k (Var an_e t) ;
                                  return $ Let an_e t anf_e anf_res
                               od))
End

Theorem mapM_cong:
  ∀l1 l2 f f'.
    l1 = l2 ∧ (∀x. MEM x l2 ⇒ f x = f' x) ⇒ mapM f l1 = mapM f' l2
Proof
  simp[] >>
  Induct >>
  rw[mapM_cons] >>
  metis_tac[]
QED

val _ = DefnBase.export_cong "mapM_cong"

(*A-normalization algorithm for cexp expressions.
  Originally from https://dl.acm.org/doi/10.1145/173262.155113*)
Definition normalize_def:
  (* normalize : 'a cexp -> ('a CONT) -> ('a anf) S *)
  (*values, call k on them*)
    (normalize (Var d x : 'a cexp) (k: 'a CONT) =
         k ((Var d x) : 'a anf))
  ∧ (normalize (Lam d args body)   (k: 'a CONT) = do
         anf_b <- (normalize body (return)) ;
         k $ Lam d args anf_b
      od)
  (*exprs*)
  ∧ (normalize (Let d v a b) (k: 'a CONT) =
         normalize a (λ anf_a.
             do anf_b <- (normalize b k) ;
                return $ Let d v anf_a anf_b
             od ))
  ∧ (normalize ((Case d e v cases):'a cexp) (k: 'a CONT) =
         normalize e $ let_bind (λ anf_e.
            do anf_cases <- mapM (λ(n,args,body). do
                                    anf_b <- normalize body (return) ;
                                    return $ (n,args,anf_b) ;
                                  od) cases;
               return $ Let d v anf_e (Case d v anf_cases)
             od ))
  ∧ (normalize (App  d f  es) (k : 'a CONT) =
         normalize f $ let_bind (λ anf_f.
            normalize_names es (λ anf_es.
                      k (App d anf_f anf_es))))
  ∧ (normalize (Prim d op es) (k : 'a CONT) =
         normalize_names es (λ anf_es.
             k (Prim d op anf_es)))
  ∧ (normalize (pure_cexp$Letrec d binds body) (k : 'a CONT) =
         normalize body (λ anf_body.
            do anf_binds <- mapM (λ(n,f). do
                                   anf_f <- normalize f (return) ;
                                   return $ (n,anf_f) ;
                                od) binds;
               return (Letrec d anf_binds anf_body)
            od ))
    (* normalize_name e k = normalize e (let_bind k) *)
  ∧ (normalize_names [] k = k [])
  ∧ (normalize_names (e::es) k = normalize e $ let_bind (λ anf_e.
                               normalize_names es (λ anf_es.
                                 k (anf_e::anf_es))))
Termination
  WF_REL_TAC ‘measure (λx. case x of INL(a,b) => cexp_size ARB a | INR(a,b) => cexp6_size ARB a)’ >>
  rw[] >>
  imp_res_tac cexp_size_lemma >>
  pop_assum(qspec_then ‘ARB’ mp_tac) >>
  DECIDE_TAC
End

(*
    (* TODO: removing mutual recursion from normalize_def*)

    (* normalize_names [] k = k [] *)
    (* normalize_names (e::es) k = normalize e $ let_bind (λ anf_e.
                               normalize_names es (λ anf_es.
                                 k (anf_e::anf_es))) *)
    (*move k to rhs*)

    normalize_names [] k = k []
    normalize_names (e::es) k = normalize e $ let_bind (λ anf_e.
                               normalize_names es (λ anf_es.
                                 k (anf_e::anf_es)))

    (* (λ anf_es. k (anf_e::anf_es)) ≡ (k o (CONS anf_e)) *)

    normalize_names [] = (λ k. k []) (*base case*)
    normalize_names (e::es) = (*fold step*)
        (λ k. normalize e $
               let_bind (λ x. normalize_names es (k o (CONS x))))

    (* ??? *)

    normalize_names es =
        FOLDR (λ e r. (λ k. normalize e $
                             let_bind (λ x. r (k o (CONS x)))))
              (λ k. k []) es

    (*eta-contraction*)

    normalize_names =
       FOLDR (λ e r. (λ k. normalize e $
                             let_bind (λ x. r (k o (CONS x)))))
             (λ k. k [])
*)



Definition fresh_state_def:
  fresh_state s avoid
    ⇔ s.base ∉ avoid ∧ (∀ ss. (STRCAT s.base ss) ∉ avoid)
End

(*given a fresh starting state, new_vname produces a fresh vname*)
Theorem new_vname_freshness:
  ∀ s avoid. fresh_state s avoid
         ⇒ FST (new_vname s) ∉ avoid
Proof
  rw[] \\ fs[fresh_state_def,new_vname_def]
  \\ EVAL_TAC \\ rw[] \\ fs[]
QED

(*new_vname does not alter the freshness of the state*)
Theorem new_vname_fresh_state_mono:
  ∀ s avoid. fresh_state s avoid
           ⇒ fresh_state (SND (new_vname s)) avoid
Proof
  rw[] \\ fs[fresh_state_def,new_vname_def]
  \\ EVAL_TAC \\ fs[]
QED

Definition fresh_var_substr_def:
   fresh_var_substr v avoid =
       if(¬MEM v avoid ∧ FOLDR MAX 0 (MAP LENGTH avoid) < LENGTH v)
           then v
           else (fresh_var_substr (v ++ "'") avoid)
Termination
  WF_REL_TAC ‘measure (λ(v,xs). (LENGTH (FLAT xs) + 1) - LENGTH v)’
  \\ Induct \\ fs[] \\ rw[] \\ fs[] \\ res_tac \\ fs[]
End

Theorem fresh_var_substr_correctness:
   ∀ v l. let x = fresh_var_substr v l
          in ¬MEM x l ∧ (∀ ss. ¬MEM (STRCAT x ss) l)
Proof
  recInduct fresh_var_substr_ind \\ rw[] \\ fs[]
  \\ once_rewrite_tac [fresh_var_substr_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ CCONTR_TAC \\ fs[]
  \\ Induct_on ‘avoid’ \\ fs[]
QED

Definition start_state_def:
  start_state e =
      <| base  :=
         fresh_var_substr ".res_" (  freevars_l  (exp_of e)
                                  ++ boundvars_l (exp_of e))
       ; vname_index := 0
       |>
End

Triviality start_state_fresh_state:
  ∀ e. fresh_state
           (start_state e)
           (freevars (exp_of e) ∪ boundvars (exp_of e))
Proof
  rw[]
  \\ fs[fresh_state_def,start_state_def]
  \\ qspecl_then [‘".res_"’
                 ,‘freevars_l (exp_of e) ++ boundvars_l (exp_of e)’]
                 mp_tac fresh_var_substr_correctness
  \\ fs[freevars_equiv,boundvars_equiv]
QED

Definition anf_of_def:
  anf_of e = normalize e (return) (start_state e)
End



(*

TODO: to write a function anf_of and prove:

  ∀e. e ≅ exp_of (anf_of e)

The anf function should use var_set from pure_varsTheory to represent
a set of variable names for efficiency, since anf_of is part of the
implementation of the compiler.

Every Let in the generated anf ought to bind a unqiue name. Ideally,
all new names should have a recognisable prefix like "." so that we
can easily see which names are generated.

The following should also hold:

  freevars (exp_of (anf_of e)) = freevars e

*)


val _ = export_theory();
