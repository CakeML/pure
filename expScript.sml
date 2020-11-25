
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory configTheory ;

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

Definition closed_def:
  closed e = (freevars e = [])
End

val _ = export_theory ();
