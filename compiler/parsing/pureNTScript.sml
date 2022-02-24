open HolKernel Parse boolLib bossLib;

val _ = new_theory "pureNT";

Datatype:
  ppegnt = nDecls | nDecl | nTyBase | nTy | nTyConDecl | nTyApp
         | nPat | nAPat | nFunRHS
         | nExp | nExpEQ | nLSafeExp | nLSafeExpEQ | nIExp | nIExpEQ
         | nFExp | nFExpEQ | nFExp2 | nAExp | nAxpEQ
         | nLit | nOp
         | nEqBindSeq | nEqBind | nValBinding
End

val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:ppegnt``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  recurse ntlist
end

Theorem pureNTs_distinct[compute] = LIST_CONJ distinct_ths

val _ = export_theory();
