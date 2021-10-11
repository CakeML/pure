open HolKernel Parse boolLib bossLib
open boolSimps
open grammarTheory finite_mapTheory
open locationTheory
open listTheory rich_listTheory

val _ = new_theory "ispegs"

(* Based on HOL's core PEG theory, which is based on
     Koprowski and Binzstok, "TRX: A Formally Verified Parser Interpreter".
     LMCS vol 7, no. 2. 2011.
     DOI: 10.2168/LMCS-7(2:18)2011
   and merging in ideas from
     Michael D. Adams, "Principled Parsing for Indentation-Sensitive Languages"
     POPL 2013
     DOI: 10.1145/2429069.2429129
*)

(* relations are attached to symbols in the grammar, indicating the relation
   between the symbol's indentation and that of the non-terminal.
   So, if a symbol has lrGT attached, it means that that symbol's indentation
   must be greater than the indentation of the non-terminal.

   Of course, the question arises, what *is* the indentation of the
   non-terminal. If the first symbol in its RHS has an lrEQ
   constraint/relation, then it's clear that the NT's indentation is the
   indentation of that first symbol.  This is a common case, and Adams denotes
   this by writing |nt| (and note that if the first symbols of the RHS are
   nullable, you may need to generate a slow of extra rules for |nt})
 *)
Datatype:
  locrel = lrEQ | lrGE | lrGT | lrOK
End

Definition evalrel_def[simp]:
  (evalrel lrEQ p c ⇔ p = c) ∧
  (evalrel lrGE p c ⇔ p ≤ c) ∧
  (evalrel lrGT p c ⇔ p < c) ∧
  (evalrel lrOK p c ⇔ T)
End

Datatype:
  ispegsym =
    empty 'c
  | any  ('a # locs -> 'c)
  | tok ('a -> bool) ('a # locs -> 'c) locrel
  | nt ('b inf) ('c -> 'c) locrel
  | seq ispegsym ispegsym ('c  -> 'c -> 'c)
  | choice ispegsym ispegsym ('c + 'c -> 'c)
  | rpt ispegsym ('c list -> 'c)
  | not ispegsym 'c
  | error 'e
End

Datatype:
  ispeg = <| start : ('a,'b,'c,'e) ispegsym ;
             anyEOF : 'e ;
             tokFALSE : 'e ; tokEOF : 'e;
             notFAIL : 'e;
             iFAIL : 'e;
             rules : 'b inf |-> ('a,'b,'c,'e) ispegsym |>
End

(* a locpred encodes a predicate that is true of an indentation;
   use lpxLT 0 for a bottom/always-false value
 *)
Datatype:
  locpred = lpTOP | lpxLT num | lpxEQ num
End
Overload lpBOT = “lpxLT 0”

Definition rel_at_col_def[simp]:
  rel_at_col lrOK c = lpTOP ∧
  rel_at_col lrGE c = lpxLT (c + 1) ∧
  rel_at_col lrGT c = lpxLT c ∧
  rel_at_col lrEQ c = lpxEQ c
End

Definition loccol_def[simp]:
  loccol (POSN r c) = c ∧
  loccol UNKNOWNpt = 0 ∧
  loccol EOFpt = 0
End

Datatype:
  pegresult = Success 'a 'c ((locs # 'e) option) locpred
            | Failure locs 'e
End
Definition isSuccess_def[simp]:
  isSuccess (Success _ _ _ _) = T ∧
  isSuccess (Failure _ _) = F
End
Definition isFailure_def[simp]:
  isFailure (Success _ _ _ _) = F ∧
  isFailure (Failure _ _) = T
End

Definition resultmap_def[simp]:
  resultmap f (Success a c eo p) = Success a (f c) eo p ∧
  resultmap f (Failure fl fe) = Failure fl fe
End
Theorem resultmap_EQ_Success :
  resultmap f r = Success a x eo p ⇔ ∃x0. r = Success a x0 eo p ∧ x = f x0
Proof
  Cases_on ‘r’ >> simp[] >> metis_tac[]
QED

Theorem resultmap_EQ_Failure[simp]:
  (resultmap f r = Failure fl fe ⇔ r = Failure fl fe) ∧
  (Failure fl fe = resultmap f r ⇔ r = Failure fl fe)
Proof
  Cases_on ‘r’ >> simp[] >> metis_tac[]
QED

Theorem resultmap_I[simp]:
  resultmap I r = r
Proof
  Cases_on ‘r’ >> simp[]
QED

Definition MAXerr_def:
  MAXerr (fl1, fe1) (fl2, fe2) =
  if locsle fl1 fl2 then (fl2, fe2) else (fl1,fe1)
End

Definition optmax_def:
  optmax f NONE NONE = NONE ∧
  optmax f NONE (SOME x) = SOME x ∧
  optmax f (SOME x) NONE = SOME x ∧
  optmax f (SOME x) (SOME y) = SOME (f x y)
End

Theorem result_cases[local] = TypeBase.nchotomy_of “:(α,β,γ) pegresult”

Overload EOF[local] = “Locs EOFpt EOFpt”
Definition sloc_def:
  sloc [] = EOF ∧
  sloc (h::t) = SND h
End

Theorem sloc_thm[simp]:
  sloc [] = EOF ∧
  sloc ((c,l) :: t) = l
Proof
  simp[sloc_def]
QED

Definition evalpred_def[simp]:
  evalpred lpTOP n = T ∧
  evalpred (lpxLT m) n = (n < m) ∧
  evalpred (lpxEQ m) n = (m = n)
End

Theorem evalpred_EQ_BOT:
  (evalpred p = λn. F) ⇔ p = lpBOT
Proof
  simp[FUN_EQ_THM] >> Cases_on ‘p’ >> simp[] >> eq_tac >> simp[] >>
  CONV_TAC CONTRAPOS_CONV >> simp[] >> strip_tac >>
  rename [‘_ < n’] >> qexists_tac ‘n - 1’ >> simp[]
QED

Definition conjpred_def[simp]:
  conjpred lpTOP p = p ∧
  conjpred p lpTOP = p ∧
  conjpred (lpxLT m) (lpxLT n) = lpxLT (MIN m n) ∧
  conjpred (lpxLT m) (lpxEQ n) = (if n < m then lpxEQ n else lpxLT 0) ∧
  conjpred (lpxEQ m) (lpxLT n) = (if m < n then lpxEQ m else lpxLT 0) ∧
  conjpred (lpxEQ m) (lpxEQ n) = if m = n then lpxEQ m else lpxLT 0
End

Theorem conjTOP_ID[simp]:
  conjpred lpTOP p = p ∧
  conjpred p lpTOP = p
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem conjBOT_BOT[simp]:
  conjpred lpBOT p = lpBOT ∧
  conjpred p lpBOT = lpBOT
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem conjpred_correct:
  evalpred (conjpred p q) n ⇔ evalpred p n ∧ evalpred q n
Proof
  Cases_on ‘p’ >> simp[] >> Cases_on ‘q’ >> simp[] >>
  rw[]
QED

Definition comppred_def[simp]:
  comppred lrOK (lpxLT n) = (if n = 0 then lpBOT else lpTOP) ∧
  comppred lrOK p = lpTOP ∧
  comppred lrEQ p = p ∧
  comppred lrGE (lpxEQ m) = (* m >= _, i.e., *) lpxLT (m + 1) ∧
  comppred lrGE (lpxLT m) = lpxLT m ∧
  comppred lrGE lpTOP = lpTOP ∧
  comppred lrGT (lpxEQ m) = lpxLT m ∧
  comppred lrGT (lpxLT m) = (if m ≤ 1 then lpBOT else lpxLT (m - 1)) ∧
  comppred lrGT lpTOP = lpTOP
End

Theorem comppred_lpTOP[simp]:
  comppred R lpTOP = lpTOP
Proof
  Cases_on ‘R’ >> simp[]
QED

Theorem comppred_EQ_TOP:
  comppred R P = lpTOP ⇔
    P = lpTOP ∨ R = lrOK ∧ (case P of lpxLT n => 0 < n | _ => T)
Proof
  Cases_on ‘R’ >> Cases_on ‘P’ >> simp[] >> rw[]
QED

Theorem comppred_correct:
  evalpred (comppred R P) p ⇔
    ∃c. evalpred P c ∧ evalrel R p c
Proof
  Cases_on ‘P’ >> simp[] >> Cases_on ‘R’ >> simp[]
  >- irule_at Any arithmeticTheory.LESS_EQ_REFL
  >- irule_at Any prim_recTheory.LESS_SUC_REFL
  >- (eq_tac >> strip_tac >> simp[] >> first_x_assum $ irule_at Any >> simp[])
  >- (rw[] >> eq_tac >> strip_tac >> simp[] >>
      first_x_assum $ irule_at Any >> simp[])
  >- (rw[] >> rename [‘_ < m’] >> Cases_on ‘m’ >> gvs[] >>
      irule_at Any prim_recTheory.LESS_SUC_REFL)
QED

Inductive ispeg_eval:
[~empty:]
  (∀s c. ispeg_eval G (s, empty c) (Success s c NONE lpTOP)) ∧
[~nt_success:]
  (∀n s s' r eo P R f.
     n ∈ FDOM G.rules ∧ ispeg_eval G (s, G.rules ' n) (Success s' r eo P) ⇒
     ispeg_eval G (s, nt n f R) (Success s' (f r) eo (comppred R P))) ∧
[~nt_failure:]
  (∀n s fl fe R f.
     n ∈ FDOM G.rules ∧ ispeg_eval G (s, G.rules ' n) (Failure fl fe) ⇒
     ispeg_eval G (s, nt n f R) (Failure fl fe)) ∧
[~any_success:]
  (∀h t f. ispeg_eval G (h::t, any f) (Success t (f h) NONE lpTOP)) ∧
[~any_failure:]
  (∀f. ispeg_eval G ([], any f) (Failure EOF G.anyEOF)) ∧
[~tok_success:]
  (∀tk l1 l2 t P f R.
     P tk ⇒
     ispeg_eval G ((tk,Locs l1 l2)::t, tok P f R)
              (Success t (f (tk,Locs l1 l2)) NONE (rel_at_col R $ loccol l1))) ∧
[~tok_failureF:]
  (∀h t P f R.
     ¬P (FST h) ⇒
     ispeg_eval G (h::t, tok P f R) (Failure (SND h) G.tokFALSE)) ∧
[~tok_failureEOF:]
  (∀P f R. ispeg_eval G ([], tok P f R) (Failure EOF G.tokEOF)) ∧
[~not_success:]
  (∀e s c fr.
     ispeg_eval G (s, e) fr ∧ isFailure fr ⇒
     ispeg_eval G (s, not e c) (Success s c NONE lpTOP)) ∧
[~not_failure:]
  (∀e s r c.
     ispeg_eval G (s, e) r ∧ isSuccess r ⇒
     ispeg_eval G (s, not e c) (Failure (sloc s) G.notFAIL))  ∧
[~seq_fail1:]
  (∀e1 e2 s f fl fe.
     ispeg_eval G (s, e1) (Failure fl fe) ⇒
     ispeg_eval G (s, seq e1 e2 f) (Failure fl fe)) ∧
[~seq_fail2:]
  (∀e1 e2 P f s0 eo s1 c1 fl fe.
     ispeg_eval G (s0, e1) (Success s1 c1 eo P) ∧
     ispeg_eval G (s1, e2) (Failure fl fe) ⇒
     ispeg_eval G (s0, seq e1 e2 f) (Failure fl fe)) ∧
[~seq_failindent:]
  (∀e1 e2 s0 s1 s2 c1 c2 f eo1 eo2 P1 P2.
     ispeg_eval G (s0, e1) (Success s1 c1 eo1 P1) ∧
     ispeg_eval G (s1, e2) (Success s2 c2 eo2 P2) ∧
     conjpred P1 P2 = lpBOT ⇒
     ispeg_eval G (s0, seq e1 e2 f) (Failure (sloc s0) G.iFAIL)) ∧
[~seq_success:]
  (∀e1 e2 s0 s1 s2 c1 c2 f eo1 eo2 P1 P2.
     ispeg_eval G (s0, e1) (Success s1 c1 eo1 P1) ∧
     ispeg_eval G (s1, e2) (Success s2 c2 eo2 P2) ∧
     conjpred P1 P2 ≠ lpBOT ⇒
     ispeg_eval G (s0, seq e1 e2 f) (Success s2 (f c1 c2) eo2 $ conjpred P1 P2)) ∧
[~choice_fail:]
  (∀e1 e2 s f fl1 fe1 fl2 fe2.
     ispeg_eval G (s, e1) (Failure fl1 fe1) ∧
     ispeg_eval G (s, e2) (Failure fl2 fe2) ⇒
     ispeg_eval G (s, choice e1 e2 f)
              (UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2)))) ∧
[~choice_success1:]
  (∀e1 e2 s0 f s r eo P.
     ispeg_eval G (s0, e1) (Success s r eo P) ⇒
     ispeg_eval G (s0, choice e1 e2 f) (Success s (f (INL r)) eo P)) ∧
[~choice_success2:]
  (∀e1 e2 s0 s r eo f fl fe P.
     ispeg_eval G (s0, e1) (Failure fl fe) ∧
     ispeg_eval G (s0, e2) (Success s r eo P) ⇒
     ispeg_eval G (s0, choice e1 e2 f)
              (Success s (f (INR r)) (optmax MAXerr (SOME (fl,fe)) eo) P)) ∧
[~error:]
  (∀e s. ispeg_eval G (s, error e) (Failure (sloc s) e)) ∧
[~rpt:]
  (∀e f s s1 list err P.
     ispeg_eval_list G lpTOP (s, e) (s1,list,err,P) ⇒
     ispeg_eval G (s, rpt e f) (Success s1 (f list) (SOME err) P)) ∧
[~list_nil:]
  (∀e s fl fe P. ispeg_eval G (s, e) (Failure fl fe) ⇒
                 ispeg_eval_list G P (s, e) (s,[],(fl,fe),P)) ∧
[~list_nilindent:]
  (∀e s0 s r eo P0 P.
     ispeg_eval G (s0, e) (Success s r eo P) ∧ conjpred P0 P = lpBOT ⇒
     ispeg_eval_list G P0 (s0, e) (s0,[],(sloc s0,G.iFAIL),P0)) ∧
[~list_cons:]
  (∀e eo0 eo s0 s1 s2 c cs P0 P1 P2.
     ispeg_eval G (s0, e) (Success s1 c eo0 P1) ∧ conjpred P0 P1 ≠ lpBOT ∧
     ispeg_eval_list G (conjpred P0 P1) (s1, e) (s2,cs,eo,P2) ⇒
     ispeg_eval_list G P0 (s0, e) (s2,c::cs,eo,P2))
End

val fprod = HO_REWR_CONV pairTheory.FORALL_PROD
Theorem ispeg_eval_strongind' =
  ispeg_eval_strongind
    |> Q.SPECL [`G`, `\es0 r. P1 (FST es0) (SND es0) r`,
                ‘\p es0 sr. P2 p (FST es0) (SND es0) (FST sr)
                               (FST $ SND sr)
                               (SND $ SND sr)’]
    |> SIMP_RULE (srw_ss()) []
    |> UNDISCH |> CONJ_PAIR
    |> (SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD] ##
        CONV_RULE (BINDER_CONV fprod THENC
                   LAST_FORALL_CONV (fprod THENC LAST_FORALL_CONV fprod)))
    |> uncurry CONJ
    |> SIMP_RULE (srw_ss()) []
    |> DISCH_ALL;

Theorem UNCURRY_Failure_EQ_Success[simp]:
  UNCURRY Failure fle ≠ Success s r eo p
Proof
  Cases_on ‘fle’ >> simp[]
QED

Theorem IS_PREFIX_MEM:
  l1 ≼ l2 ∧ MEM e l1 ⇒ MEM e l2
Proof
  simp[IS_PREFIX_APPEND, PULL_EXISTS]
QED

Theorem ispeg_eval_suffix0[local]:
  (∀s0 e sr.
     ispeg_eval G (s0,e) sr ⇒
     (∀s r eo p.
       sr = Success s r eo p ⇒ IS_SUFFIX s0 s) ∧
     (∀fl fe. sr = Failure fl fe ∧ fl ≠ EOF ⇒ MEM fl (MAP SND s0))) ∧
  ∀P s0 e s rl err.
    ispeg_eval_list G P (s0,e) (s,rl,err) ⇒ IS_SUFFIX s0 s
Proof
  HO_MATCH_MP_TAC ispeg_eval_strongind' THEN
  SRW_TAC [][IS_SUFFIX_compute, IS_PREFIX_APPEND3, IS_PREFIX_REFL] THEN
  gvs[resultmap_EQ_Success] >~
  [‘UNCURRY Failure (MAXerr (fl1,_) (fl2,_))’]
  >- (Cases_on ‘locsle fl1 fl2’ >> gvs[MAXerr_def]) >~
  [‘isSuccess sr’, ‘MEM (sloc s0) (MAP SND s0)’]
  >- (Cases_on ‘s0’ >> gvs[sloc_def]) >~
  [‘sloc s0 ≠ EOF’, ‘MEM (sloc s0) (MAP SND s0)’]
  >- (Cases_on ‘s0’ >> gvs[sloc_def]) >~
  [‘sloc s0 ≠ EOF’, ‘MEM (sloc s0) (MAP SND s0)’]
  >- (Cases_on ‘s0’ >> gvs[sloc_def]) >~
  [‘MEM fl (MAP SND s0)’, ‘REVERSE s1 ≼ REVERSE s0’]
  >- (gvs[MEM_MAP] >>
      metis_tac[IS_PREFIX_MEM, MEM_REVERSE]) >>
  metis_tac [IS_PREFIX_TRANS]
QED

(* Theorem 3.1 *)
Theorem ispeg_eval_suffix =
  ispeg_eval_suffix0 |> SIMP_RULE (srw_ss() ++ DNF_ss) [GSYM CONJ_ASSOC]

(* Theorem 3.2 *)
Theorem peg_deterministic:
  (∀s0 e sr. ispeg_eval G (s0,e) sr ⇒
             ∀sr'. ispeg_eval G (s0,e) sr' ⇔ sr' = sr) ∧
  ∀P s0 e s rl err.
    ispeg_eval_list G P (s0,e) (s,rl,err) ⇒
    ∀srl'. ispeg_eval_list G P (s0,e) srl' ⇔ srl' = (s,rl,err)
Proof
  HO_MATCH_MP_TAC ispeg_eval_strongind' THEN SRW_TAC [][] THEN
  ONCE_REWRITE_TAC [ispeg_eval_cases] THEN SRW_TAC [][] THEN
  csimp[] >>
  TRY (Q.MATCH_ASSUM_RENAME_TAC ‘isSuccess result’ >>
       Cases_on ‘result’ >> fs[]) THEN
  TRY (Q.MATCH_ASSUM_RENAME_TAC ‘isFailure result’ >>
       Cases_on ‘result’ >> fs[]) >>
  rename [‘_ = Failure (SND h) _’] >> Cases_on ‘h’ >> gs[]
QED

Theorem peg_nullable_lpTOP:
  (∀s0 e sr. ispeg_eval G (s0,e) sr ⇒
             ∀r eo p. sr = (Success s0 r eo p) ⇒ p = lpTOP) ∧
  (∀P s0 e s rl err.
     ispeg_eval_list G P (s0,e) (s,rl,err) ⇒ s0 = s ⇒ SND err = P)
Proof
  ho_match_mp_tac ispeg_eval_strongind' >> rw[]
  >- (drule_then assume_tac $ cj 1 ispeg_eval_suffix >>
      rev_drule_then assume_tac $ cj 1 ispeg_eval_suffix >>
      gvs[IS_SUFFIX_compute] >> dxrule_all IS_PREFIX_ANTISYM >> rw[]) >>
  drule_then assume_tac $ cj 3 ispeg_eval_suffix >>
  drule_then assume_tac $ cj 1 ispeg_eval_suffix >>
  gvs[IS_SUFFIX_compute] >> dxrule_all IS_PREFIX_ANTISYM >> rw[]
QED

(* Lemma 3.3 *)
Theorem peg_badrpt:
  ispeg_eval G (s0,e) (Success s0 r eo p) ⇒
  ∀r. ¬ispeg_eval G (s0, rpt e f) r
Proof
  strip_tac >> simp[Once ispeg_eval_cases] >> rw[] >>
  rpt strip_tac >> dxrule_then assume_tac $ cj 2 peg_deterministic  >>
  drule ispeg_eval_list_cons >> simp[] >>
  drule $ cj 1 peg_nullable_lpTOP >> simp[] >> rw[] >>
  first_assum (irule_at Any o iffRL) >> simp[]
QED

Inductive peg0:
  (∀c. peg0 G (empty c)) ∧

  (* any *)
  (∀f. peggt0 G (any f)) ∧
  (∀f. pegfail G (any f)) ∧

  (* tok *)
  (∀t f R. peggt0 G (tok t f R)) ∧
  (∀t f R. pegfail G (tok t f R)) ∧
  (∀t f R. R ≠ lrOK ⇒ pegnontop G (tok t f R)) ∧

  (* rpt *)
  (∀e f. pegfail G e ⇒ peg0 G (rpt e f)) ∧
  (∀e f. peggt0 G e ⇒ peggt0 G (rpt e f)) ∧
  (∀e f. pegnontop G e ⇒ pegnontop G (rpt e f)) ∧

  (* nt rules *)
  (∀n f R. n ∈ FDOM G.rules ∧ peg0 G (G.rules ' n) ⇒
           peg0 G (nt n f R)) ∧
  (∀n f R. n ∈ FDOM G.rules ∧ peggt0 G (G.rules ' n) ⇒
         peggt0 G (nt n f R)) ∧
  (∀n f R. n ∈ FDOM G.rules ∧ pegfail G (G.rules ' n) ⇒
           pegfail G (nt n f R)) ∧
  (∀n f R. n ∈ FDOM G.rules ∧ pegnontop G (G.rules ' n) ⇒
           pegnontop G (nt n f R)) ∧

  (* seq rules *)
[pegfail_seq:]
  (∀e1 e2 f. pegfail G e1 ∨ (peg0 G e1 ∧ pegfail G e2) ∨
             (peggt0 G e1 ∧ pegfail G e2) ⇒
             pegfail G (seq e1 e2 f)) ∧
  (∀e1 e2 f. peggt0 G e1 ∧ (peg0 G e2 ∨ peggt0 G e2) ∨
             (peg0 G e1 ∨ peggt0 G e1) ∧ peggt0 G e2 ⇒
             peggt0 G (seq e1 e2 f)) ∧
  (∀e1 e2 f. peg0 G e1 ∧ peg0 G e2 ⇒ peg0 G (seq e1 e2 f)) ∧
  (∀e1 e2 f. pegnontop G e1 ∨ pegnontop G e2 ⇒ pegnontop G (seq e1 e2 f)) ∧

  (* choice rules *)
  (∀e1 e2 f. peg0 G e1 ∨ (pegfail G e1 ∧ peg0 G e2) ⇒
             peg0 G (choice e1 e2 f)) ∧
  (∀e1 e2 f. pegfail G e1 ∧ pegfail G e2 ⇒ pegfail G (choice e1 e2 f)) ∧
  (∀e1 e2 f. peggt0 G e1 ∨ (pegfail G e1 ∧ peggt0 G e2) ⇒
             peggt0 G (choice e1 e2 f)) ∧
  (∀e1 e2 f. pegnontop G e1 ∨ pegnontop G e2 ⇒ pegnontop G (choice e1 e2 f)) ∧

  (* not *)
  (∀e c. pegfail G e ⇒ peg0 G (not e c)) ∧
  (∀e c. peg0 G e ∨ peggt0 G e ⇒ pegfail G (not e c)) ∧

  (* error *)
  (∀e. pegfail G (error e)) ∧

  (* general *)
  ∀e. pegnontop G e ⇒ pegfail G e
End

Theorem peg0_error[simp]:
  ¬peg0 G (error e)
Proof
  simp[Once peg0_cases]
QED

Theorem ispeg_eval_suffix':
  ispeg_eval G (s0,e) (Success s c eo p) ⇒
  s0 = s ∨ IS_SUFFIX s0 s ∧ LENGTH s < LENGTH s0
Proof
  strip_tac >>
  drule_then strip_assume_tac (cj 1 ispeg_eval_suffix) >>
  Cases_on `s0 = s` >> gvs[] >>
  gvs[IS_SUFFIX_compute] >>
  imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
  qsuff_tac `LENGTH s ≠ LENGTH s0` >- (strip_tac >> decide_tac) >>
  strip_tac >>
  metis_tac [IS_PREFIX_LENGTH_ANTI, LENGTH_REVERSE, REVERSE_REVERSE]
QED

Theorem ispeg_eval_list_suffix':
  ispeg_eval_list G p (s0, e) (s,rl,err) ⇒
  s0 = s ∨ IS_SUFFIX s0 s ∧ LENGTH s < LENGTH s0
Proof
  strip_tac >>
  drule_then strip_assume_tac (cj 3 ispeg_eval_suffix) >>
  Cases_on `s0 = s` >> gvs[] >>
  fs[IS_SUFFIX_compute] >> imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
  qsuff_tac `LENGTH s ≠ LENGTH s0` >- (strip_tac >> decide_tac) >> strip_tac >>
  metis_tac [IS_PREFIX_LENGTH_ANTI, LENGTH_REVERSE, REVERSE_REVERSE]
QED

fun rule_match th = FIRST (List.mapPartial (total MATCH_MP_TAC)
                           (th |> SPEC_ALL |> CONJUNCTS))

Theorem FORALL_result:
  (∀r. P r) ⇔ (∀a c eo p. P (Success a c eo p)) ∧ (∀fl fe. P (Failure fl fe))
Proof
  rw[EQ_IMP_THM] >> Cases_on ‘r’ >> simp[]
QED

Theorem EXISTS_result:
  (∃r. P r) ⇔ (∃a c eo p. P (Success a c eo p)) ∨ (∃fl fe. P (Failure fl fe))
Proof
  rw[EQ_IMP_THM] >- (Cases_on ‘r’ >> metis_tac[]) >> metis_tac[]
QED

Theorem lemma4_1a0[local]:
  (∀s0 e r.
     ispeg_eval G (s0, e) r ⇒
     (∀c eo p. r = Success s0 c eo p ⇒ peg0 G e) ∧
     (∀s c eo p. r = Success s c eo p ∧ p ≠ lpTOP ⇒ pegnontop G e) ∧
     (isFailure r ⇒ pegfail G e) ∧
     (∀s c eo p. r = Success s c eo p ∧ LENGTH s < LENGTH s0 ⇒ peggt0 G e)) ∧
  (∀P0 s0 e s rl errp.
     ispeg_eval_list G P0 (s0,e) (s,rl,errp) ⇒
     ∀err P. errp = (err,P) ⇒
             (s0 = s ⇒ pegfail G e ∨ P0 = lpBOT) ∧
             (LENGTH s < LENGTH s0 ⇒ peggt0 G e) ∧
             (P0 = lpTOP ∧ P ≠ lpTOP ⇒ pegnontop G e))
Proof
  ho_match_mp_tac ispeg_eval_strongind' >>
  simp[peg0_rules, FORALL_result, pairTheory.FORALL_PROD] >>
  rpt conj_tac >> rpt gen_tac >~
  [‘pegnontop G (nt n f R)’]
  >- (simp[comppred_EQ_TOP] >> rpt strip_tac >> rule_match peg0_rules >>
      simp[]) >~
  [‘pegnontop G (tok P f R)’]
  >- (rpt strip_tac >> rule_match peg0_rules >> strip_tac >>
      gvs[]) >~
  [‘pegfail G (not e f)’]
  >- (rpt strip_tac >> imp_res_tac ispeg_eval_suffix' >> gvs[peg0_rules]) >~
  [‘pegfail G (seq e1 e2 f)’, ‘ispeg_eval G (s1,e2) (Failure _ _)’]
  >- (rpt strip_tac >> metis_tac[peg0_rules, ispeg_eval_suffix']) >~
  [‘pegfail G (seq e1 e2 f)’, ‘ispeg_eval G (s0,e1) (Success s1 r1 eo1 p1)’,
   ‘ispeg_eval G (s1,e2) (Success s2 r2 eo2 p2)’]
  >- (rpt strip_tac >> irule pegfail_seq >>
      imp_res_tac ispeg_eval_suffix' >> gvs[]
      >- (drule $ cj 1 peg_nullable_lpTOP >> rw[] >>
          rev_drule $ cj 1 peg_nullable_lpTOP >> rw[] >> gvs[])
      >- (‘p2 = lpTOP’ by (irule $ cj 1 peg_nullable_lpTOP >> metis_tac[]) >>
          gvs[peg0_rules])
      >- (‘p1 = lpTOP’ by (irule $ cj 1 peg_nullable_lpTOP >> metis_tac[]) >>
          gvs[peg0_rules]) >>
      ‘¬(p1 = lpTOP ∧ p2 = lpTOP)’ by (strip_tac >> gvs[]) >>
      metis_tac[peg0_rules]) >~
  [‘peggt0 G (seq e1 e2 f)’]
  >- (rpt strip_tac >> rule_match peg0_rules
      >- (gvs[] >>
          drule $ cj 1 ispeg_eval_suffix >> rev_drule $ cj 1 ispeg_eval_suffix>>
          simp[IS_SUFFIX_compute] >> rpt strip_tac >>
          dxrule_all IS_PREFIX_ANTISYM >> simp[])
      >- metis_tac[conjpred_def]
      >- (drule $ cj 1 ispeg_eval_suffix' >> rw[] >> gvs[] >>
          rev_drule $ cj 1 ispeg_eval_suffix' >> rw[] >> gvs[])) >~
  [‘ispeg_eval G (s0,e) (Success s1 r eo1 p1)’,
   ‘ispeg_eval_list G (conjpred p0 p1) (s1,e) _’]
  >- (rpt strip_tac >~
      [‘s0 = s’, ‘ispeg_eval _ (s0,e) (Success s1 _ _ _ )’]
      >- (drule $ cj 1 ispeg_eval_suffix >>
          drule $ cj 3 ispeg_eval_suffix >> rw[IS_SUFFIX_compute] >>
          dxrule_all IS_PREFIX_ANTISYM >> simp[] >> strip_tac >> gvs[])
      >- (drule ispeg_eval_suffix' >> rw[] >> simp[]) >>
      gvs[] >> metis_tac[]) >>
  rpt strip_tac >>
  rename [‘conjpred p1 p2 = lpBOT’, ‘p1 = lpBOT’] >>
  Cases_on ‘p2 = lpTOP’ >> gvs[peg0_rules]
QED

Theorem lemma4_1a = lemma4_1a0 |> SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO]

Inductive wfpeg:
  (∀n f R. n ∈ FDOM G.rules ∧ wfpeg G (G.rules ' n) ⇒ wfpeg G (nt n f R)) ∧
[~_empty[simp]:]
  (∀c. wfpeg G (empty c)) ∧
[~_any[simp]:]
  (∀f. wfpeg G (any f)) ∧
[~tok[simp]:]
  (∀t f R. wfpeg G (tok t f R)) ∧
[~_error[simp]:]
  (∀e. wfpeg G (error e)) ∧
  (∀e c. wfpeg G e ⇒ wfpeg G (not e c)) ∧
  (∀e1 e2 f. wfpeg G e1 ∧ (peg0 G e1 ⇒ wfpeg G e2) ⇒
             wfpeg G (seq e1 e2 f)) ∧
  (∀e1 e2 f. wfpeg G e1 ∧ wfpeg G e2 ⇒ wfpeg G (choice e1 e2 f)) ∧
  (∀e f. wfpeg G e ∧ ¬peg0 G e ⇒ wfpeg G (rpt e f))
End

Definition subexprs_def[simp]:
  (subexprs (any f1) = { any f1 }) ∧
  (subexprs (empty c) = { empty c }) ∧
  (subexprs (tok t f2 R) = { tok t f2 R }) ∧
  (subexprs (error e) = { error e }) ∧
  (subexprs (nt s f R) = { nt s f R}) ∧
  (subexprs (not e c) = not e c INSERT subexprs e) ∧
  (subexprs (seq e1 e2 f3) = seq e1 e2 f3 INSERT subexprs e1 ∪ subexprs e2) ∧
  (subexprs (choice e1 e2 f4) =
    choice e1 e2 f4 INSERT subexprs e1 ∪ subexprs e2) ∧
  (subexprs (rpt e f5) = rpt e f5 INSERT subexprs e)
End

Theorem subexprs_included[simp]: e ∈ subexprs e
Proof Induct_on `e` >> srw_tac[][subexprs_def]
QED

Definition Gexprs_def:
  Gexprs G = BIGUNION (IMAGE subexprs (G.start INSERT FRANGE G.rules))
End

Theorem start_IN_Gexprs[simp]:
  G.start ∈ Gexprs G
Proof
  simp[Gexprs_def, subexprs_included]
QED

val wfG_def = Define`wfG G ⇔ ∀e. e ∈ Gexprs G ⇒ wfpeg G e`;

Theorem IN_subexprs_TRANS:
  ∀a b c. a ∈ subexprs b ∧ b ∈ subexprs c ⇒ a ∈ subexprs c
Proof
  Induct_on `c` >> simp[] >> rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem Gexprs_subexprs:
  e ∈ Gexprs G ⇒ subexprs e ⊆ Gexprs G
Proof
  simp_tac (srw_ss() ++ DNF_ss) [Gexprs_def, pred_setTheory.SUBSET_DEF] >>
  strip_tac >> metis_tac [IN_subexprs_TRANS]
QED

Theorem IN_Gexprs_E:
  (not e c ∈ Gexprs G ⇒ e ∈ Gexprs G) ∧
  (seq e1 e2 f ∈ Gexprs G ⇒ e1 ∈ Gexprs G ∧ e2 ∈ Gexprs G) ∧
  (choice e1 e2 f2 ∈ Gexprs G ⇒ e1 ∈ Gexprs G ∧ e2 ∈ Gexprs G) ∧
  (rpt e f3 ∈ Gexprs G ⇒ e ∈ Gexprs G)
Proof
  rpt strip_tac >> imp_res_tac Gexprs_subexprs >> fs[] >>
  metis_tac [pred_setTheory.SUBSET_DEF, subexprs_included]
QED

val pair_CASES = pairTheory.pair_CASES
val option_CASES = optionTheory.option_nchotomy

Theorem reducing_ispeg_eval_makes_list[local]:
  (∀s. LENGTH s < n ⇒ ∃r. ispeg_eval G (s, e) r) ∧ ¬peg0 G e ∧ LENGTH s0 < n ⇒
  ∀P. ∃s' rl err p'. ispeg_eval_list G P (s0,e) (s',rl,err,p')
Proof
  strip_tac >> completeInduct_on `LENGTH s0` >> rw[] >>
  gs[SF DNF_ss] >>
  ‘(∃fl fe. ispeg_eval G (s0,e) (Failure fl fe)) ∨
   ∃s1 c eo p. ispeg_eval G (s0,e) (Success s1 c eo p)’
    by metis_tac [result_cases]
  >- metis_tac [ispeg_eval_list_nil] >>
  `s0 ≠ s1` by metis_tac [lemma4_1a] >>
  `LENGTH s1 < LENGTH s0` by metis_tac [ispeg_eval_suffix'] >>
  Cases_on ‘conjpred P p = lpBOT’
  >- (irule_at Any ispeg_eval_list_nilindent >> metis_tac[]) >>
  irule_at Any ispeg_eval_list_cons >> gs[pairTheory.EXISTS_PROD] >>
  metis_tac []
QED

Theorem ispeg_eval_total:
  wfG G ⇒ ∀s e. e ∈ Gexprs G ⇒ ∃r. ispeg_eval G (s,e) r
Proof
  simp[wfG_def] >> strip_tac >> gen_tac >>
  completeInduct_on ‘LENGTH s’ >>
  gs[SF DNF_ss] >> rpt strip_tac >>
  ‘wfpeg G e’ by metis_tac[] >>
  Q.UNDISCH_THEN ‘e ∈ Gexprs G’ mp_tac >>
  pop_assum mp_tac >> qid_spec_tac ‘e’ >>
  Induct_on ‘wfpeg’ >> rw[] >~
  [‘nt n f R ∈ Gexprs G’]
  >- (‘G.rules ' n ∈ Gexprs G’
        suffices_by (strip_tac >>
                     first_x_assum $ drule_then
                                   $ qx_choose_then ‘result’ strip_assume_tac >>
                     Cases_on ‘result’ >>
                     metis_tac [ispeg_eval_nt_success, ispeg_eval_nt_failure])>>
      dsimp[Gexprs_def, FRANGE_DEF] >>
      metis_tac [subexprs_included]) >~
  [‘empty _ ∈ Gexprs G’] >- metis_tac [ispeg_eval_empty] >~
  [‘any _ ∈ Gexprs G’]
  >- metis_tac [ispeg_eval_any_success, ispeg_eval_any_failure,list_CASES] >~
  [‘ispeg_eval _ (s, tok t f R)’]
  >- (Cases_on ‘s’ >- metis_tac [ispeg_eval_tok_failureEOF] >>
      rename [‘ispeg_eval _ (h::rest, tok _ _ _)’] >>
      ‘∃l1 l2 t. h = (t, Locs l1 l2)’
        by metis_tac[pair_CASES, TypeBase.nchotomy_of “:locs”] >> gvs[] >>
      metis_tac[ispeg_eval_tok_success, ispeg_eval_tok_failureF, pairTheory.FST,
                pairTheory.SND]) >~
  [‘error _’] >- metis_tac[ispeg_eval_error] >~
  [‘not _ _’] >- metis_tac [ispeg_eval_not_success, result_cases, IN_Gexprs_E,
                            isFailure_def, isSuccess_def,
                            ispeg_eval_not_failure] >~
  [‘seq e1 e2 f ∈ Gexprs G’]
  >- (‘e1 ∈ Gexprs G’ by imp_res_tac IN_Gexprs_E >>
      ‘(∃fl fe. ispeg_eval G (s,e1) (Failure fl fe))  ∨
       ∃s' c eo p. ispeg_eval G (s,e1) (Success s' c eo p)’
        by metis_tac[result_cases]
      >- (irule_at Any ispeg_eval_seq_fail1 >> metis_tac[]) >>
      Cases_on ‘s' = s’
      >- (‘peg0 G e1’ by metis_tac [lemma4_1a] >>
          ‘e2 ∈ Gexprs G’ by imp_res_tac IN_Gexprs_E >>
          metis_tac [ispeg_eval_rules, result_cases]) >>
      ‘LENGTH s' < LENGTH s’ by metis_tac [ispeg_eval_suffix'] >>
      ‘∃r'. ispeg_eval G (s',e2) r'’ by metis_tac [IN_Gexprs_E] >>
      metis_tac [result_cases, ispeg_eval_rules]) >~
  [‘choice e1 e2’]
  >- (drule_then strip_assume_tac (cj 3 IN_Gexprs_E) >> fs[] >>
      metis_tac [ispeg_eval_rules, result_cases]) >~
  [‘rpt e f’]
  >- (imp_res_tac IN_Gexprs_E >>
      ‘(∃fl fe. ispeg_eval G (s, e) (Failure fl fe)) ∨
       ∃s' c eo p. ispeg_eval G (s,e) (Success s' c eo p)’
        by metis_tac [result_cases]
      >- (‘ispeg_eval_list G lpTOP (s,e) (s,[],(fl,fe), lpTOP)’
            by metis_tac [ispeg_eval_list_nil] >>
          metis_tac [ispeg_eval_rpt]) >>
      ‘s' ≠ s’ by metis_tac [lemma4_1a] >>
      ‘LENGTH s' < LENGTH s’ by metis_tac [ispeg_eval_suffix'] >>
      irule_at Any ispeg_eval_rpt >>
      Cases_on ‘p = lpBOT’
      >- (irule_at Any ispeg_eval_list_nilindent >> gvs[] >>
          goal_assum drule) >>
      irule_at Any ispeg_eval_list_cons >> simp[] >>
      rpt (goal_assum drule) >>
      metis_tac[reducing_ispeg_eval_makes_list])
QED

(* derived and useful PEG forms *)
Definition pegf_def:  pegf sym f = seq sym (empty ARB) (λl1 l2. f l1)
End

val ignoreL_def = Define`
  ignoreL s1 s2 = seq s1 s2 (λa b. b)
`;
val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "ignoreL",
                          tok = "~>"}

val ignoreR_def = Define`
  ignoreR s1 s2 = seq s1 s2 (λa b. a)
`;
val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "ignoreR",
                          tok = "<~"}

val choicel_def = Define`
  (choicel [] = not (empty ARB) ARB) ∧
  (choicel (h::t) = choice h (choicel t) (λs. sum_CASE s I I))
`;

val checkAhead_def = Define`
  checkAhead P s = not (not (tok P ARB lrOK) ARB) ARB ~> s
`;

Theorem ispeg_eval_seq_SOME:
  ispeg_eval G (i0, seq s1 s2 f) (Success i r eo p) ⇔
    ∃i1 r1 r2 eo1 p1 p2.
      ispeg_eval G (i0, s1) (Success i1 r1 eo1 p1) ∧
      ispeg_eval G (i1, s2) (Success i r2 eo p2) ∧ r = f r1 r2 ∧
      p = conjpred p1 p2 ∧ p ≠ lpBOT
Proof simp[Once ispeg_eval_cases] >> metis_tac[]
QED

Theorem ispeg_eval_seq_NONE:
  ispeg_eval G (i0, seq s1 s2 f) (Failure fl fe) ⇔
  ispeg_eval G (i0, s1) (Failure fl fe) ∨
  (∃i r eo p. ispeg_eval G (i0,s1) (Success i r eo p) ∧
            ispeg_eval G (i,s2) (Failure fl fe)) ∨
  (∃i1 i2 r1 r2 eo1 eo2 p1 p2.
     ispeg_eval G (i0,s1) (Success i1 r1 eo1 p1) ∧
     ispeg_eval G (i1,s2) (Success i2 r2 eo2 p2) ∧
     conjpred p1 p2 = lpBOT ∧ fl = sloc i0 ∧ fe = G.iFAIL)
Proof
  simp[Once ispeg_eval_cases] >> metis_tac[]
QED

Theorem ispeg_eval_tok_NONE =
  “ispeg_eval G (i, tok P f R) (Failure fl fe)”
    |> SIMP_CONV (srw_ss()) [Once ispeg_eval_cases]

Theorem ispeg_eval_tok_SOME:
  ispeg_eval G (i0, tok P f R) (Success i r eo p) ⇔
  ∃h l1 l2. P h ∧ i0 = (h,Locs l1 l2)::i ∧ r = f (h,Locs l1 l2) ∧ eo = NONE ∧
            p = rel_at_col R (loccol l1)
Proof simp[Once ispeg_eval_cases, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem ispeg_eval_empty[simp]:
  ispeg_eval G (i, empty r) x ⇔ x = Success i r NONE lpTOP
Proof simp[Once ispeg_eval_cases]
QED

(* Theorem ispeg_eval_NT_SOME:
  ispeg_eval G (i0,nt N f) (Success i r eo) ⇔
  ∃r0. r = f r0 ∧ N ∈ FDOM G.rules ∧
       ispeg_eval G (i0,G.rules ' N) (Success i r0 eo)
Proof simp[Once ispeg_eval_cases, resultmap_EQ_Success, PULL_EXISTS]
QED

Theorem ispeg_eval_choice:
  ∀x.
     ispeg_eval G (i0, choice s1 s2 f) x ⇔
      (∃sr. ispeg_eval G (i0, s1) sr ∧ isSuccess sr ∧
            x = resultmap (f o INL) sr) ∨
      (∃i r eo fl fe.
         ispeg_eval G (i0, s1) (Failure fl fe) ∧
         ispeg_eval G (i0, s2) (Success i r eo) ∧
         x = Success i (f $ INR r) (optmax MAXerr (SOME (fl,fe)) eo)) ∨
      ∃fl1 fe1 fl2 fe2.
        ispeg_eval G (i0, s1) (Failure fl1 fe1) ∧
        ispeg_eval G (i0, s2) (Failure fl2 fe2) ∧
        x = UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2))
Proof
  simp[Once ispeg_eval_cases, SimpLHS] >> simp[EXISTS_result, FORALL_result] >>
  metis_tac[]
QED

Theorem ispeg_eval_choicel_NIL[simp]:
  ispeg_eval G (i0, choicel []) x = (x = Failure (sloc i0) G.notFAIL)
Proof
  simp[choicel_def, Once ispeg_eval_cases]
QED

Theorem ispeg_eval_choicel_CONS:
  ∀x. ispeg_eval G (i0, choicel (h::t)) x ⇔
        ∃y.
          ispeg_eval G (i0, h) y ∧
          case y of
            Success i r eo => x = Success i r eo
          | Failure fl1 fe1 =>
              ∃z. ispeg_eval G (i0, choicel t) z ∧
                  case z of
                    Success i r eo =>
                      x = Success i r (optmax MAXerr (SOME(fl1,fe1)) eo)
                  | Failure fl2 fe2 =>
                      x = UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2))
Proof
  simp[choicel_def, SimpLHS, Once ispeg_eval_cases] >>
  dsimp[FORALL_result, EXISTS_result] >>
  metis_tac[]
QED

Theorem ispeg_eval_rpt:
  ispeg_eval G (i0, rpt s f) x ⇔
    ∃i l err. ispeg_eval_list G (i0,s) (i,l,err) ∧ x = Success i (f l) (SOME err)
Proof simp[Once ispeg_eval_cases, SimpLHS] >> metis_tac[]
QED

val ispeg_eval_list = Q.store_thm(
  "ispeg_eval_list",
  `ispeg_eval_list G (i0, e) (i, r, err) ⇔
     (∃fl fe. ispeg_eval G (i0, e) (Failure fl fe) ∧ i = i0 ∧ r = [] ∧
             err = (fl,fe)) ∨
     (∃i1 rh rt eo0.
        ispeg_eval G (i0, e) (Success i1 rh eo0) ∧
        ispeg_eval_list G (i1, e) (i, rt, err) ∧ r = rh::rt)`,
  simp[Once ispeg_eval_cases, SimpLHS] >> metis_tac[]);

Theorem pegfail_empty[simp]:
  pegfail G (empty r) = F
Proof simp[Once peg0_cases]
QED

Theorem peg0_empty[simp]:
  peg0 G (empty r) = T
Proof simp[Once peg0_cases]
QED

Theorem peg0_not[simp]:
  peg0 G (not s r) ⇔ pegfail G s
Proof simp[Once peg0_cases, SimpLHS]
QED

Theorem peg0_choice[simp]:
  peg0 G (choice s1 s2 f) ⇔ peg0 G s1 ∨ pegfail G s1 ∧ peg0 G s2
Proof
  simp[Once peg0_cases, SimpLHS]
QED

Theorem peg0_choicel[simp]:
  (peg0 G (choicel []) = F) ∧
  (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))
Proof
  simp[choicel_def]
QED

Theorem peg0_seq[simp]:
  peg0 G (seq s1 s2 f) ⇔ peg0 G s1 ∧ peg0 G s2
Proof simp[Once peg0_cases, SimpLHS]
QED

Theorem peg0_tok[simp]:
  peg0 G (tok P f) = F
Proof
  simp[Once peg0_cases]
QED

Theorem peg0_pegf[simp]:
  peg0 G (pegf s f) = peg0 G s
Proof
  simp[pegf_def]
QED
*)
val _ = export_theory()
