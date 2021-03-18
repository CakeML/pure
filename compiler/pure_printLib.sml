(*
   Library for pretty printing and basic parsing of cexp
*)
structure pure_printLib :> pure_printLib =
struct

open HolKernel Parse boolLib bossLib;
open pure_printTheory intLib;

fun dest_QUOTE (q: term frag list) =
  let
    fun drop_until [] = []
      | drop_until (x::xs) = if x = #")" then xs else drop_until xs;
  in
    case q of
      [QUOTE str] => (String.implode o drop_until o String.explode) str
    | _ => failwith "not a single QUOTE"
  end;

fun print_cexp tm =
  “str_of ^tm” |> EVAL |> concl |> rand |> stringSyntax.fromHOLstring |> print;

fun parse_cexp s =
  mk_comb(“parse_cexp”,stringLib.fromMLstring s)
  |> EVAL |> concl |> rand;

fun parse_prog s =
  mk_comb(“parse_prog”,stringLib.fromMLstring s)
  |> EVAL |> concl |> rand;

val Cexp = parse_cexp o dest_QUOTE
val Prog = parse_prog o dest_QUOTE

end
