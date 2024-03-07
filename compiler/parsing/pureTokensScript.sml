open HolKernel Parse boolLib bossLib;

open tokensTheory

val _ = new_theory "pureTokens";

val _ = set_grammar_ancestry ["tokens"];

Overload PragmaT = “TyvarT”

val _ = export_theory();
