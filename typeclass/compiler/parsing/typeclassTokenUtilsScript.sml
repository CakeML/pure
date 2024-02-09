open HolKernel Parse boolLib bossLib;

open tokenUtilsTheory

val _ = new_theory "pureTokenUtils";

val _ = set_grammar_ancestry ["tokenUtils"]
val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Definition capname_def:
  capname nm ⇔
  do
    c1 <- oHD nm ;
    assert $ isUpper c1
  od = SOME ()
End

Definition capname_tok_def:
  capname_tok tk <=>
  do
    s <- destAlphaT tk;
    assert $ capname s
  od = SOME ()
End

Definition keywords_def:
  keywords = ["data"; "where"; "let"; "in"; "if"; "then"; "else"; "do";]
End

Definition lcname_def:
  lcname s ⇔
    do
      assert (¬MEM s keywords);
      c1 <- oHD s;
      assert $ isLower c1
    od = SOME ()
End


Definition lcname_tok_def:
  lcname_tok tk <=>
  do
    s <- destAlphaT tk;
    assert $ lcname s
  od = SOME ()
End

Definition isSymbolOpT_def:
  isSymbolOpT t ⇔
  do
    s <- destSymbolT t ;
    assert (s ≠ "<-" ∧ s ≠ "::" ∧ s ≠ "->" ∧ s ≠ "`");
  od = SOME ()
End

val _ = export_theory();
