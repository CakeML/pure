structure cases =
struct

datatype pat = pv of string | pc of string * pat list | pUS

datatype exp =
         eLet of string * string * exp | eBase of int | eNoMatch |
         eMatch of string * (pat * exp) list


type problem = ((string * pat) list * exp) list

fun A(p1,p2) = pc("Add", [p1, p2])
fun M(p1,p2) = pc("Mul", [p1, p2])
fun S p = pc ("Succ", [p])
val Z = pc ("Zero", [])

val jjeg1:problem =
    [([("a", A(Z, Z))], eBase 1),
     ([("a", M(Z, pv "X"))], eBase 2),
     ([("a", A(S(pv "X"), pv "Y"))], eBase 3),
     ([("a", M(pv "X", Z))], eBase 4),
     ([("a", M(A(pv "X", pv "Y"), pv "Z"))], eBase 5),
     ([("a", A(pv "X", Z))], eBase 6),
     ([("a", pv "X")], eBase 7)]

fun push_var (eqns, rhs) =
    let fun foldthis (eqn, (eqns, rhs)) =
            case eqn of
                (v, pv pnm) => (eqns, eLet (pnm,v,rhs))
              | _ => (eqn::eqns, rhs)
        val (eqs', rhs') = List.foldl foldthis ([],rhs) eqns
    in
      (List.rev eqs', rhs')
    end

fun push_vars (p : problem) : problem = map push_var p

fun pat_arity (pc (_, args)) = List.length args
  | pat_arity _ = raise Fail "pat_arity on p. variable"
fun pat_con (pc(cnm, _)) = cnm
  | pat_con _ = raise Fail "pat_con on p. variable"

fun pluck P [] = NONE
  | pluck P (h::t) = if P h then SOME (h, t)
                     else Option.map (fn (x,t) => (x, h::t)) (pluck P t)


fun lift testvar cnm vars (p : problem) : problem * problem =
    let
      fun lift1 (c as (eqns, rhs), (A,B)) =
          case pluck (fn (tv, p) => tv = testvar) eqns of
              NONE => (c::A, c::B)
            | SOME ((_, pc(cnm', args')), other_tests : (string * pat) list) =>
              if cnm' = cnm then
                ((ListPair.zip (vars, args') @ other_tests, rhs) :: A, B)
              else (A, c::B)
            | SOME ((_, pv _), _) => raise Fail "lift1: found pat-var binding"
      val (A,B) = List.foldl lift1 ([], []) p
    in
      (List.rev A, List.rev B)
    end

fun bumpany k e m =
    case Binarymap.peek(m,k) of
        NONE => Binarymap.insert(m,k,(1,e))
      | SOME (c,e0) => Binarymap.insert(m,k,(c+1,e0))
fun bumpex k m =
    case Binarymap.peek(m,k) of
        NONE => m
      | SOME (c,e) => Binarymap.insert(m,k,(c+1,e))

fun maxcount M =
    let fun foldthis (k, ce, NONE) = SOME ce
          | foldthis (k, ce as (c,e), A as SOME (c0,e0)) =
            if c > c0 then SOME ce else A
    in
      Binarymap.foldl foldthis NONE M
    end

fun heuristic eqns rest =
    let val M0 = Binarymap.mkDict (pair_compare(String.compare, String.compare))
        fun foldthis (e as (vnm, pc(cnm, _)), M) = bumpany (vnm,cnm) e M
          | foldthis (_, M) = M
        val M1 = List.foldl foldthis M0 eqns
        fun foldthis2 (e as (vnm, pc(cnm, _)), M) = bumpex (vnm,cnm) M
          | foldthis2 (_, M) = M
        val M2 = List.foldl
                   (fn ((es,exp), A) => List.foldl foldthis2 A es) M1 rest
    in
      #2 (valOf (maxcount M2))
    end


fun get_firstbranch (p0 : problem)  =
    let val p = push_vars p0
    in
      case p of
          ([], rhs) :: rest => rhs
        | (eqns, rhs) :: rest =>
          let val (tvar, pat) = heuristic eqns rest
              val newvars =
                  List.tabulate(pat_arity pat, (fn i => tvar ^ Int.toString i))
              val cnm = pat_con pat
              val patarg_vector = map pv newvars
              val pat1 = pc(cnm, patarg_vector)
              val (A, B) = lift tvar cnm newvars p
          in
            eMatch (tvar, [(pc (cnm, patarg_vector), get_firstbranch A),
                           (pUS, get_firstbranch B)])
          end
        | [] => eNoMatch
    end

fun updlast [] rep = rep
  | updlast [h] rep = rep
  | updlast (h::t) rep = h::updlast t rep

fun merge_dumbUS e =
    case e of
        eMatch (testv1, pes) =>
        let val pes' = map (apsnd merge_dumbUS) pes
        in
          case last pes' of
              (pUS, eMatch (testv2, uspes)) =>
              if testv1 = testv2 then
                eMatch (testv1, updlast pes' uspes)
              else eMatch (testv1, pes')
            | _ => eMatch (testv1, pes')
        end
      | eLet(v1,v2,e) => eLet(v1,v2,merge_dumbUS e)
      | _ => e

val jjeg2 : problem =
    [([("a", A (A(pv "X", pv "Y"), Z))], eBase 1),
     ([("a", A (M(pv "X", pv "Y"), Z))], eBase 2),
     ([("a", A (pv "X", M(pv "Y", pv "Z")))], eBase 3),
     ([("a", A (pv "X", A(pv "Y", pv "Z")))], eBase 4),
     ([("a", A (pv "X", Z))], eBase 5)]

val sol2 = merge_dumbUS $ get_firstbranch jjeg2

fun uniq_pfx p slist =
    case List.filter (String.isPrefix p) slist of
        [] => p
      | ss => uniq_pfx (p ^ "%") ss

end
