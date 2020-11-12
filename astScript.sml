
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory bagTheory;

val _ = new_theory "ast";

(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)
Type fname = “:string”  (* function name *)

(*configuration record for the parametric atoms.

   parAtomOp:
     It takes an element of type 'a (from AtomOp) and returns a
     function that takes a "'b list" element and SOME b if the
     number of arguments is correct, NONE otherwise

*)
Datatype:
  conf = <| parAtomOp  : 'a -> 'b list -> 'b option; |>
End

Datatype:
  op = If               (* if-expression                            *)
     | Cons string      (* datatype constructor                     *)
     | IsEq string num  (* compare cons tag and num of args         *)
     | Proj string num  (* reading a field of a constructor         *)
     | AtomOp 'a        (* primitive parametric operator over Atoms *)
     | Lit 'b           (* parametric literal Atom                  *)
End

Datatype:
  exp = Var vname                     (* variable                   *)
      | Prim (('a,'b) op) (exp list)  (* primitive operations       *)
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

(* a call-by-name semantics in a denotational semantics style *)

(* would like to have:
Codatatype:
  ('a,'b) v = Atom 'b
          | Constructor string (('a,'b) v) list)
          | Closure vname ('a exp)
          | Diverge
          | Error
End
*)

Datatype:
  v_prefix = Atom' 'b
           | Constructor' string
           | Closure' vname (('a,'b) exp)
           | Diverge'
           | Error'
End

Definition v_rep_ok_def:
  v_rep_ok v ⇔
    ∀a ts.
      Branch a ts ∈ subtrees v ⇒
        case a of
          Constructor' s => LFINITE ts
        | _ => ts = LNIL
End

Theorem v_inhabited[local]:
  ∃f. v_rep_ok f
Proof
  qexists_tac ‘Branch Error' LNIL’
  \\ simp [v_rep_ok_def, subtrees]
QED

val v_tydef = new_type_definition ("v", v_inhabited);

val repabs_fns = define_new_type_bijections
  {name = "v_absrep",
   ABS  = "v_abs",
   REP  = "v_rep",
   tyax = v_tydef};

val v_absrep = CONJUNCT1 repabs_fns;
val v_repabs = CONJUNCT2 repabs_fns;

Theorem v_rep_ok_v_rep[local,simp]:
  ∀v. v_rep_ok (v_rep v)
Proof
  rw [v_repabs, v_absrep]
QED

Theorem v_abs_11[local]:
  v_rep_ok v1 ∧ v_rep_ok v2 ⇒
    (v_abs v1 = v_abs v2) = (v1 = v2)
Proof
  rw [v_repabs, EQ_IMP_THM] \\ fs []
QED

Theorem v_rep_11[local]:
  (v_rep v1 = v_rep v2) = (v1 = v2)
Proof
  metis_tac [v_absrep]
QED

(*
 * RUBRIK
 *)

Definition Atom_rep_def:
  Atom_rep = λb. Branch (Atom' b) LNIL
End

Definition Constructor_rep_def:
  Constructor_rep = λs ts. Branch (Constructor' s) (fromList ts)
End

Definition Closure_rep_def:
  Closure_rep = λs x. Branch (Closure' s x) LNIL
End

Definition Diverge_rep_def:
  Diverge_rep = Branch Diverge' LNIL
End

Definition Error_rep_def:
  Error_rep = Branch Error' LNIL
End

(*
 * RUBRIK
 *)

Definition Atom_def:
  Atom b = v_abs (Atom_rep b)
End

Definition Constructor_def:
  Constructor s ts = v_abs (Constructor_rep s (MAP v_rep ts))
End

Definition Closure_def:
  Closure s x = v_abs (Closure_rep s x)
End

Definition Diverge_def:
  Diverge = v_abs Diverge_rep
End

Definition Error_def:
  Error = v_abs Error_rep
End

(*
 * RUBRIK
 *)

Theorem LSET_fromList:
  ∀l. LSET (fromList l) = set l
Proof
  Induct \\ rw [fromList_def]
QED


Theorem v_rep_ok_Atom[local]:
  ∀b. v_rep_ok (Atom_rep b)
Proof
  rw [Atom_rep_def, v_rep_ok_def, subtrees]
QED

Theorem v_rep_ok_Constructor[local]:
  ∀s ts. v_rep_ok (Constructor_rep s (MAP v_rep ts))
Proof
  rw [v_rep_ok_def]
  \\ fs [subtrees, Constructor_rep_def, LFINITE_fromList]
  \\ ‘v_rep_ok x’
    by fs [LSET_fromList, MEM_MAP]
  \\ fs [v_rep_ok_def]
QED

Theorem v_rep_ok_Closure[local]:
  ∀s x. v_rep_ok (Closure_rep s x)
Proof
  rw [Closure_rep_def, v_rep_ok_def, subtrees]
QED

Theorem v_rep_ok_Diverge[local]:
  v_rep_ok Diverge_rep
Proof
  rw [Diverge_rep_def, v_rep_ok_def, subtrees]
QED

Theorem v_rep_ok_Error[local]:
  v_rep_ok Error_rep
Proof
  rw [Error_rep_def, v_rep_ok_def, subtrees]
QED

(*
 * Prove one-one theorems for constructors.
 *)

Theorem Atom_rep_11[local]:
  ∀x y. Atom_rep x = Atom_rep y ⇔ x = y
Proof
  rw [Atom_rep_def]
QED

Theorem Constructor_rep_11[local]:
  ∀s1 t1 s2 t2.
    Constructor_rep s1 t1 = Constructor_rep s2 t2 ⇔ s1 = s2 ∧ t1 = t2
Proof
  rw [Constructor_rep_def]
QED

Theorem Closure_rep_11[local]:
  ∀n1 x1 n2 x2.
    Closure_rep n1 x1 = Closure_rep n2 x2 ⇔ n1 = n2 ∧ x1 = x2
Proof
  rw [Closure_rep_def]
QED

Theorem Atom_11:
  ∀x y. Atom x = Atom y ⇔ x = y
Proof
  rw [Atom_def, v_rep_ok_Atom, Atom_rep_11, v_abs_11]
QED

Theorem Constructor_11:
  ∀s1 t1 s2 t2.
    Constructor s1 t1 = Constructor s2 t2 ⇔ s1 = s2 ∧ t1 = t2
Proof
  rw [Constructor_def]
  \\ eq_tac \\ strip_tac \\ fs []
  \\ qmatch_asmsub_abbrev_tac ‘_ x1 = _ x2’
  \\ ‘v_rep_ok x1 ∧ v_rep_ok x2’
    by (unabbrev_all_tac \\ rw []
        \\ irule v_rep_ok_Constructor)
  \\ unabbrev_all_tac
  \\ fs [v_abs_11, Constructor_rep_11]
  \\ ‘INJ v_rep (set t1 ∪ set t2) 𝕌(:('a,'b) v_prefix ltree)’
    by simp [pred_setTheory.INJ_DEF, v_rep_11]
  \\ drule INJ_MAP_EQ \\ fs []
QED

Theorem Closure_11:
  ∀n1 x1 n2 x2.
    Closure n1 x1 = Closure n2 x2 ⇔ n1 = n2 ∧ x1 = x2
Proof
  rw [Closure_def, v_rep_ok_Closure, Closure_rep_11, v_abs_11]
QED

Theorem v_11 = LIST_CONJ [Atom_11, Closure_11, Constructor_11];

(*
 * Prove distinctness for constructors.
 *)

Theorem v_distinct:
  ALL_DISTINCT [Atom b; Closure n x; Constructor s t; Error; Diverge]
Proof
  rw [Atom_def, Closure_def, Constructor_def, Error_def, Diverge_def]
  \\ rw [v_rep_ok_Atom,
         v_rep_ok_Closure,
         v_rep_ok_Constructor,
         v_rep_ok_Diverge,
         v_rep_ok_Error,
         v_abs_11]
  \\ rw [Atom_rep_def,
         Closure_rep_def,
         Constructor_rep_def,
         Diverge_rep_def,
         Error_rep_def]
QED

Theorem v_distinct = SIMP_RULE list_ss [GSYM CONJ_ASSOC] v_distinct;

(*
 * Prove nchotomy and cases for constructors.
 *)

Theorem rep_exists[local]:
  v_rep_ok v ⇒
    (∃b. v = Atom_rep b) ∨
    (∃s t. v = Constructor_rep s t) ∨
    (∃n x. v = Closure_rep n x) ∨
    v = Diverge_rep ∨
    v = Error_rep
Proof
  rw [v_rep_ok_def]
  \\ Cases_on ‘v’
  \\ pop_assum (qspecl_then [‘a’, ‘ts’] mp_tac)
  \\ simp [subtrees, Atom_rep_def, Constructor_rep_def, Closure_rep_def,
     Diverge_rep_def, Error_rep_def]
  \\ Cases_on ‘a’ \\ fs []
  \\ metis_tac [to_fromList]
QED

Theorem v_cases:
  ∀v.
    (∃b. v = Atom b) ∨
    (∃s t. v = Constructor s t) ∨
    (∃n x. v = Closure n x) ∨
    v = Diverge ∨
    v = Error
Proof
  simp [GSYM v_rep_11, Atom_def, Constructor_def, Closure_def,
        Diverge_def, Error_def]
  \\ gen_tac
  \\ qabbrev_tac ‘x = v_rep v’
  \\ ‘v_rep_ok x’ by simp [Abbr ‘x’]
  \\ drule rep_exists
  \\ rw [] \\ fs []
  \\ TRY (metis_tac [v_repabs])
  \\ disj2_tac \\ disj1_tac
  \\ qexists_tac ‘s’
  \\ qexists_tac ‘MAP v_abs t’
  \\ simp [MAP_MAP_o, combinTheory.o_DEF]
  (* TODO: Clean up this part. *)
  \\ ‘EVERY v_rep_ok t’ by cheat
  \\ fs [v_repabs]
  \\ qpat_x_assum ‘_ = _’ (SUBST1_TAC o SYM)
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp [Constructor_rep_def]
  \\ fs [EVERY_MEM]
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ Induct_on ‘t’ \\ simp [v_repabs]
QED

Definition v_CASE[nocompute]:
  v_CASE v atom cons clos div err =
    case v_rep v of
      Branch (Atom' b) [||] => atom b
    | Branch (Constructor' s) ts => cons s (MAP v_abs (THE (toList ts)))
    | Branch (Closure' n x) [||] => clos n x
    | Branch Diverge' [||] => div
    | Branch Error' [||] => err
    | _ => ARB
End

Theorem v_CASE[compute]:
  v_CASE (Atom b) atom cons clos div err = atom b ∧
  v_CASE (Constructor s t) atom cons clos div err = cons s t ∧
  v_CASE (Closure n x) atom cons clos div err = clos n x ∧
  v_CASE Diverge atom cons clos div err = div ∧
  v_CASE Error atom cons clos div err = err
Proof
  rw [v_CASE, Atom_def, Constructor_def, Closure_def, Diverge_def, Error_def]
  \\ qmatch_goalsub_abbrev_tac ‘v_rep (v_abs xx)’
  \\ ‘v_rep_ok xx’
    by rw [Abbr ‘xx’, v_rep_ok_Atom, v_rep_ok_Constructor, v_rep_ok_Closure,
           v_rep_ok_Diverge, v_rep_ok_Error]
  \\ fs [v_repabs, Abbr ‘xx’, Atom_rep_def, Constructor_rep_def,
         Closure_rep_def, Diverge_rep_def, Error_rep_def, from_toList,
         MAP_MAP_o, combinTheory.o_DEF, v_absrep]
QED

Theorem v_CASE_eq:
  v_CASE v atom cons clos div err = x ⇔
    (∃b. v = Atom b ∧ atom b = x) ∨
    (∃s t. v = Constructor s t ∧ cons s t = x) ∨
    (∃n y. v = Closure n y ∧ clos n y = x) ∨
    (v = Diverge ∧ div = x) ∨
    (v = Error ∧ err = x)
Proof
  qspec_then ‘v’ strip_assume_tac v_cases \\ rw []
  \\ fs [v_CASE, v_11, v_distinct]
QED

(*
 * Register with TypeBase.
 *)

Theorem v_CASE_cong:
  ∀M M' atom cons clos div err atom' cons' clos' div' err'.
    M = M' ∧
    (∀b. M' = Atom b ⇒ atom b = atom' b) ∧
    (∀s t. M' = Constructor s t ⇒ cons s t = cons' s t) ∧
    (∀n x. M' = Closure n x ⇒ clos n x = clos' n x) ∧
    (M' = Diverge ⇒ div = div') ∧
    (M' = Error ⇒ err = err') ⇒
      v_CASE M atom cons clos div err = v_CASE M' atom' cons' clos' div' err'
Proof
  rw []
  \\ qspec_then ‘M’ strip_assume_tac v_cases
  \\ rw [] \\ fs [v_CASE]
QED

Theorem datatype_v:
  DATATYPE ((v
             (Atom : 'b -> ('a, 'b) v)
             (Constructor : string -> ('a, 'b) v list -> ('a, 'b) v)
             (Closure : string -> ('a, 'b) exp -> ('a, 'b) v)
             (Diverge : ('a, 'b) v)
             (Error : ('a, 'b) v)) : bool)
Proof
  rw [boolTheory.DATATYPE_TAG_THM]
QED

val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info
    { ax = TypeBasePure.ORIG TRUTH,
      induction = TypeBasePure.ORIG TRUTH, (* TODO: bisimulation *)
      case_def = v_CASE,
      case_cong = v_CASE_cong,
      case_eq = v_CASE_eq,
      nchotomy = v_cases,
      size = NONE,
      encode = NONE,
      lift = NONE,
      one_one = SOME v_11,
      distinct = SOME v_distinct,
      fields = [],
      accessors = [],
      updates = [],
      destructors = [],
      recognizers = [] } ]

val _ = export_theory ();


