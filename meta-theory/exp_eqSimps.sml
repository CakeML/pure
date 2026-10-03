structure exp_eqSimps :> exp_eqSimps =
struct


open HolKernel simpLib boolSimps boolLib bossLib

open pure_congruenceTheory pure_congruence_lemmasTheory

val EXPEQ_ss = let
  val rsd = {refl = exp_eq_refl, trans = exp_eq_trans,
             weakenings = [exp_eq_intro_cong],
             subsets = [],
             rewrs = [beta_equality, exp_eq_Add, Let_Var, exp_eq_IfT, Let_Var',
                      Seq_Fail, Let_Fail]}
  val frag1 = relsimp_ss rsd
  val congs = SSFRAG {
        dprocs = [], ac = [], rewrs = [], name = NONE,
        congs = [exp_eq_Lam_cong, exp_eq_App_cong, exp_eq_Let_cong_noaconv,
                 exp_eq_If_cong, exp_eq_COND_cong, exp_eq_Seq_cong
                 (* ,
                    letrec_cong'*) ],
        convs = [],
        filter = NONE}
in
  merge_ss [frag1, congs] |> name_ss "EXPEQ_ss" |> register_frag
end

end (* struct *)
