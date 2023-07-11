open HolKernel Parse boolLib bossLib;

open pureASTTheory mlstringTheory
val _ = new_theory "ast_to_shortAST";

val _ = set_grammar_ancestry ["pureAST"]

Definition assoc_def:
  assoc a [] = INL (mlstring$implode ("Unknown module: " ++ (mods_to_string a))) ∧
  assoc a ((b1, b2) :: rest) =
  if b1 = a
  then INR b2
  else assoc a rest
End

Definition assoc_opt_def:
  assoc_opt a [] = SOME a ∧
  assoc_opt a ((b1, b2) :: rest) =
  if b1 = a
  then b2
  else assoc_opt a rest
End

Definition defined_in_module_def:
  defined_in_module nm decls =
  case decls of
    [] => []
  | (declData s _ _) :: rest =>
      let id = mk_id nm s in
        (Short s, SOME id) :: (id, SOME id) :: (defined_in_module nm rest)
  | (declFunbind s _ _) :: rest =>
      let id = mk_id nm s in
        (Short s, SOME id) :: (id, SOME id) :: (defined_in_module nm rest)
  | _ :: rest => defined_in_module nm rest
End

Definition exports_def:
  exports [] = [] ∧
  exports ((module nm _ decls) :: rest) = (nm, defined_in_module nm decls) :: (exports rest)
End

Definition add_name_def:
  add_name n id [] = [(n, id)] ∧
  add_name n id ((n', id') :: rest) =
  if n = n'
  then (n, NONE) :: rest
  else (n', id') :: (add_name n id rest)
End

Definition add_names_def:
  add_names [] l = l ∧
  add_names ((n, id) :: rest) l =
  add_names rest (add_name n id l)
End

Definition imported_def:
  imported n imports exports =
  case imports of
    [] => assoc n exports
  | (import nm) :: rest =>
      case assoc nm exports of
        INL e => INL e
      | INR mdl =>
          case imported n rest exports of
            INL e => INL e
          | INR imp => INR (add_names mdl imp)
End

Definition long_to_short_def:
  long_to_short s = Short (long_name_to_string s)
End

Definition short_name_def:
  short_name imp id =
  case assoc_opt (id:long_name) (imp : ((long_name # (long_name option)) list)) of
    SOME s => s
  | NONE => Short ""
End

Definition short_name_string_def:
  short_name_string imp s = long_name_to_string (short_name imp (Short s))
End

Definition shorten_ty_def:
  (shorten_ty imp (tyOp id tys) =
   tyOp (short_name imp id) (MAP (shorten_ty imp) tys)) ∧
  shorten_ty imp (tyVar s) = tyVar s ∧
  (shorten_ty imp (tyTup tys) =
   tyTup (MAP (shorten_ty imp) tys))
Termination
  WF_REL_TAC ‘measure (λ(imp, ty). tyAST_size ty)’
End

Definition shorten_pat_def:
  (shorten_pat imp (patVar s) = patVar s) ∧
  (shorten_pat imp (patApp id l) =
   patApp (short_name imp id) (MAP (shorten_pat imp) l)) ∧
  (shorten_pat imp (patTup l) =
   patTup (MAP (shorten_pat imp) l)) ∧
  (shorten_pat imp (patLit lit) = patLit lit) ∧
  (shorten_pat imp patUScore = patUScore)
Termination
  WF_REL_TAC ‘measure (λ(imp, pat). patAST_size pat)’
End

Definition add_local_names_def:
  add_local_names (patVar v) l = (Short v, SOME (Short v)) :: l ∧
  add_local_names (patApp id []) l = l ∧
  (add_local_names (patApp id (pat::rest)) l =
   add_local_names (patApp id rest) (add_local_names pat l)) ∧
  add_local_names (patTup []) l = l ∧
  (add_local_names (patTup (pat::rest)) l =
   add_local_names (patTup rest) (add_local_names pat l)) ∧
  add_local_names (patLit _) l = l ∧
  add_local_names patUScore l = l
End

Definition shorten_exp_def:
  shorten_exp imp (expVar id) = expVar (short_name imp id) ∧
  (shorten_exp imp (expCon id l) =
   expCon (short_name imp id) (MAP (shorten_exp imp) l)) ∧
  (shorten_exp imp (expOp op l) =
   expOp op (MAP (shorten_exp imp) l)) ∧
  (shorten_exp imp (expTup l) =
   expTup (MAP (shorten_exp imp) l))∧
  (shorten_exp imp (expApp exp1 exp2) =
   expApp (shorten_exp imp exp1) (shorten_exp imp exp2)) ∧
  (shorten_exp imp (expAbs pat exp) =
   expAbs (shorten_pat imp pat) (shorten_exp (add_local_names pat imp) exp)) ∧
  (shorten_exp imp (expIf exp1 exp2 exp3) =
   expIf (shorten_exp imp exp1) (shorten_exp imp exp2) (shorten_exp imp exp3)) ∧
  shorten_exp imported (expLit lit) = expLit lit ∧
  (shorten_exp imp (expLet expdecs exp) =
   let (expdec', imp') = shorten_expdecs imp expdecs in
     expLet expdec' (shorten_exp imp' exp)) ∧
   (* expLet (MAP (shorten_expdec imp) expdec) (shorten_exp imp exp)) ∧ *)
  (shorten_exp imp (expDo dostmts exp) =
   case dostmts of
     [] => expDo [] (shorten_exp imp exp)
   | dostmt :: rest => let (do', imp') = shorten_expdostmt imp dostmt in
                         case shorten_exp imp' (expDo rest exp) of
                           expDo rest' exp' => expDo (do' :: rest') exp') ∧
  (* expDo (MAP (shorten_expdostmt imp) l) (shorten_exp imp exp)) ∧ *)
  (shorten_exp imp (expCase exp l) =
   expCase (shorten_exp imp exp)
           (MAP (λ (pat, exp). (shorten_pat imp pat, shorten_exp (add_local_names pat imp) exp)) l)) ∧

  (* (shorten_expdec imp (expdecTysig s ty) = *)
  (*  expdecTysig s (shorten_ty imp ty)) ∧ *)
  (* (shorten_expdec imp (expdecPatbind pat exp) = *)
  (*  expdecPatbind (shorten_pat imp pat) (shorten_exp imp exp)) ∧ *)
  (* (shorten_expdec imp (expdecFunbind s l exp) = *)
  (*  expdecFunbind s (MAP (shorten_pat imp) l) (shorten_exp imp exp)) ∧ *)

  (shorten_expdecs imp []) = ([], imp) ∧
  (shorten_expdecs imp (dec :: rest) =
   case dec of
     expdecTysig s ty =>
       (let (rest', imp') = shorten_expdecs imp rest in
         ((expdecTysig s (shorten_ty imp ty)) :: rest', imp'))
   | expdecPatbind pat exp =>
       (let (rest', imp') = shorten_expdecs (add_local_names pat imp) rest in
          ((expdecPatbind (shorten_pat imp pat) (shorten_exp imp exp)) :: rest', imp'))
   | expdecFunbind s pats exp =>
       let imp_fun = add_local_names (patVar s) (FOLDR add_local_names imp pats) in
         let (rest', imp') = shorten_expdecs imp_fun rest in
             (expdecFunbind s (MAP (shorten_pat imp) pats) (shorten_exp imp_fun exp)) :: rest', imp') ∧

  (shorten_expdostmt imp (expdostmtExp exp) =
   (expdostmtExp (shorten_exp imp exp), imp)) ∧
  (shorten_expdostmt imp (expdostmtBind pat exp) =
   (expdostmtBind (shorten_pat imp pat) (shorten_exp imp exp), add_local_names pat imp)) ∧
  (shorten_expdostmt imp (expdostmtLet decs) =
   let (decs', imp') = shorten_expdecs imp decs in
     (expdostmtLet decs', imp'))
Termination
  WF_REL_TAC ‘measure (λs. case s of
                             INL (_, e) => expAST_size e
                           | INR (INL (_, l)) => expAST5_size l
                           | INR (INR (_, ed)) => expdostmtAST_size ed)’
End

Definition shorten_tys_snd_def:
  shorten_ty_snd imp (s, tys) = (s, MAP (shorten_ty imp) tys)
End

Definition shorten_decl_def:
  (shorten_in_decl imp (declTysig s ty) =
   declTysig (short_name_string imp s) (shorten_ty imp ty)) ∧
  (shorten_in_decl imp (declData n l l') =
   declData (short_name_string imp n) l (MAP (shorten_ty_snd imp) l')) ∧
  (shorten_in_decl imp (declFunbind s pats exp) =
   declFunbind (short_name_string imp s) pats (shorten_exp imp exp)) ∧
  (shorten_in_decl imp (declPatbind pat exp) =
   declPatbind pat (shorten_exp imp exp))
End

Definition shorten_module_def:
  shorten_in_module exports (module nm imports decls) =
  case imported nm imports exports of
    INL e => INL e
  | INR imp => INR (module nm imports (MAP (shorten_in_decl imp) decls))
End

Definition contains_error_def:
  contains_error [] = NONE ∧
  contains_error ((INL e)::rest) = SOME e ∧
  contains_error ((INR _)::rest) = contains_error rest
End

Definition shorten_names_def:
  shorten_names modules =
  let mdls = MAP (shorten_in_module (exports modules)) modules in
  case contains_error mdls of
    SOME e => INL e
  | NONE => INR (MAP (λx. case x of INR y => y) mdls)
End

Definition remove_module_def:
  remove_module (module n imports decls) = decls
End

Definition remove_modules_def:
  remove_modules modules =
  case shorten_names modules of
    INL e => NONE
  | INR mdls => SOME (FLAT (MAP remove_module mdls))
End

val _ = export_theory();
