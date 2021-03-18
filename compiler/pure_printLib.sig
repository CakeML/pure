signature pure_printLib =
sig

    include Abbrev

    (* parsing *)

    val parse_cexp : string -> term
    val parse_prog : string -> term
    val Cexp       : term frag list -> term
    val Prog       : term frag list -> term

    (* printing *)

    val print_cexp : term -> unit

end
