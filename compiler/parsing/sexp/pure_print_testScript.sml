(*
   Pretty printing and basic parsing of cexp
*)
Theory pure_print_test
Ancestors
  pure_print
Libs
  term_tactic intLib pure_printLib

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

