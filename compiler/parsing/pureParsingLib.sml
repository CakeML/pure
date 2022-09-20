structure pureParsingLib :> pureParsingLib =
struct


local open pureParseTheory in end
val _ = computeLib.add_funs [lexer_funTheory.get_token_def,
                             listTheory.LIST_REL_def,
                             ASCIInumbersTheory.s2n_compute,
                             numposrepTheory.l2n_def]

val string_to_asts_t =
    prim_mk_const{Thy = "pureParse", Name = "string_to_asts"}

fun toASTdecls q =
    let
      val s = Portable.quote_to_string (fn _ => "") q
      val s_t = stringSyntax.fromMLstring s
      val t = mk_comb(string_to_asts_t, s_t)
    in
      t |> EVAL
        |> concl
        |> rhs
        |> rand
        |> listSyntax.dest_list
        |> #1
    end


end
