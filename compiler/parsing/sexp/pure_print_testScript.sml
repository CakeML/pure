(*
   Pretty printing and basic parsing of cexp
*)
open HolKernel Parse boolLib bossLib term_tactic;
open intLib pure_printTheory pure_printLib;

val _ = new_theory "pure_print_test";

val p = Prog ‘

(define if
  (lam (x y z) (case x temp ((True) y)
                            ((False) z))))

(define even
  (lam (n) (app if (= n (int 0))
                   (cons True)
                   (app odd (- n (int 1))))))

(define odd
  (lam (n) (app if (= n (int 0))
                   (cons False)
                   (app even (- n (int 1))))))

(app even (int 8))

’

val _ = print_cexp p

val _ = export_theory();
