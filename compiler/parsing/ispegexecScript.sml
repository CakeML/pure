open HolKernel Parse boolLib bossLib

open boolSimps

open ispegsTheory locationTheory

open rich_listTheory;

val _ = new_theory "ispegexec"

Datatype:
  kont =
    ksym (('atok,'bnt,'cvalue,'err) ispegsym) kont kont
  | appf1 ('cvalue -> 'cvalue) kont
  | appf2 ('cvalue -> 'cvalue -> 'cvalue) kont
  | lpconj kont kont
  | lpcomp locrel kont
  | setlps (locpred list) kont
  | dropErr kont
  | addErr locs 'err kont
  | cmpErrs kont
  | cmpEO ((locs # 'err) option) kont
  | returnTo (('atok#locs) list) ('cvalue option list) kont
  | restoreEO ((locs # 'err) option) kont
  | poplist ('cvalue list -> 'cvalue) kont
  | listsym (('atok,'bnt,'cvalue,'err) ispegsym)
            ('cvalue list -> 'cvalue)
            kont
  | done
  | failed
End

val poplist_aux_def = Define`
  poplist_aux acc (SOME h::t) = poplist_aux (h::acc) t ∧
  poplist_aux acc (NONE::t) = (acc,t) ∧
  poplist_aux acc [] = (acc,[]) (* should never happen *)
`;

val poplistval_def = Define`
  poplistval f l = let (values,rest) = poplist_aux [] l
                   in
                     SOME(f values) :: rest
`;

Datatype:
  evalcase = EV (('atok,'bnt,'cvalue,'err) ispegsym)
                (('atok#locs) list)
                (locpred list)
                ('cvalue option list)
                ((locs # 'err) option)
                ((locs # 'err) list)
                (('atok,'bnt,'cvalue,'err) kont)
                (('atok,'bnt,'cvalue,'err) kont)
           | AP (('atok,'bnt,'cvalue,'err) kont)
                (('atok#locs) list)
                (locpred list)
                ('cvalue option list)
                ((locs # 'err) option)
                ((locs # 'err) list)
           | Result ((('atok # locs)list, 'cvalue, 'err) pegresult)
           | Looped
End

Overload OME[local] = “optmax MAXerr”
Overload EOF[local] = “Locs EOFpt EOFpt”

Definition coreloop_def[nocompute]:
  coreloop G =
   OWHILE (λs. case s of Result _ => F
                       | _ => T)
          (λs. case s of
                   EV (empty v) i p r eo errs k fk =>
                     AP k i (lpTOP::p) (SOME v::r) eo errs
                 | EV (any tf) i p r eo errs k fk =>
                   (case i of
                        [] => let err = (EOF, G.anyEOF)
                              in
                                AP fk i p r (OME eo (SOME err)) (err::errs)
                      | h::t => AP k t (lpTOP::p) (SOME (tf h) :: r) eo errs)
                 | EV (tok P tf2 R) i ps r eo errs k fk =>
                   (case i of
                        [] => let err = (EOF, G.tokEOF)
                              in
                                AP fk i ps r (OME eo (SOME err)) (err::errs)
                      | (tk,Locs l1 l2)::t =>
                          if P tk then
                            AP k t (rel_at_col R (loccol l1)::ps)
                               (SOME (tf2 (tk,Locs l1 l2))::r) eo errs
                          else let err = (sloc i, G.tokFALSE)
                               in AP fk i ps r (OME eo (SOME err))
                                     (err::errs))
                 | EV (nt n tf3 R) i p r eo errs k fk =>
                   if n ∈ FDOM G.rules then
                     EV (G.rules ' n) i p r eo errs (lpcomp R $ appf1 tf3 k) fk
                   else
                     Looped
                 | EV (seq e1 e2 f) i p r eo errs k fk =>
                     EV e1 i p r eo errs
                        (restoreEO eo
                         (ksym e2
                          (lpconj (appf2 f k)
                           (addErr (sloc i) G.iFAIL $ cmpEO eo $ setlps p $
                            returnTo i r $ fk))
                          (setlps p $ cmpEO eo $ returnTo i r fk)))
                        fk
                 | EV (choice e1 e2 cf) i p r eo errs k fk =>
                     EV e1 i p r eo errs
                        (appf1 (cf o INL) k)
                        (returnTo i r $ setlps p $
                         ksym e2
                          (dropErr (appf1 (cf o INR) k))
                          (cmpErrs fk))
                 | EV (rpt e lf) i p r eo errs k fk =>
                     EV e i (lpTOP::p) (NONE::r) eo errs
                        (lpconj (restoreEO eo $ listsym e lf $ k)
                         (returnTo i (NONE::r) $ restoreEO eo $
                          addErr (sloc i) G.iFAIL $ poplist lf $ k))
                        (poplist lf k)
                 | EV (not e v) i p r eo errs k fk =>
                     EV e i p r eo errs
                        (restoreEO eo $ returnTo i r $ setlps p $
                         addErr (sloc i) G.notFAIL fk)
                        (restoreEO eo $ setlps (lpTOP :: p) $
                         returnTo i (SOME v::r) (dropErr k))
                 | EV (error err) i p r eo errs k fk =>
                     let err = (sloc i, err)
                     in
                       AP fk i p r (OME eo (SOME err)) (err :: errs)
                 | AP done i _ [] _ _ => Looped
                 | AP done i _ (NONE :: t) _ _ => Looped
                 | AP done i [] _ _ _ => Looped
                 | AP done i (p :: _) (SOME rv :: _) eo _ =>
                     Result (Success i rv eo p)
                 | AP failed i _ r _ [] => Looped
                 | AP failed i _ r _ ((l,e)::_) => Result (Failure l e)
                 | AP (dropErr _) i _ r _ [] => Looped
                 | AP (dropErr k) i p r eo (_ :: t) => AP k i p r eo t
                 | AP (addErr l e k) i p r eo errs =>
                     AP k i p r (OME eo (SOME (l,e))) ((l,e)::errs)
                 | AP (cmpErrs k) i p r _ [] => Looped
                 | AP (cmpErrs k) i p r _ [_] => Looped
                 | AP (cmpErrs k) i p r eo ((l2,er2)::(l1,er1)::rest) =>
                     AP k i p r eo
                        ((if locsle l1 l2 then (l2,er2) else (l1,er1)) :: rest)
                 | AP (cmpEO eo1 k) i p r eo2 [] => Looped
                 | AP (cmpEO eo1 k) i p r eo2 ((l,err)::rest) =>
                     AP k i p r (OME eo1 (SOME (l,err))) ((l,err)::rest)
                 | AP (ksym e k fk) i p r eo errs => EV e i p r eo errs k fk
                 | AP (appf1 f1 k) i p (SOME v :: r) eo errs =>
                     AP k i p (SOME (f1 v) :: r) eo errs
                 | AP (appf1 _ _) _ _ _ _ _ => Looped
                 | AP (appf2 f2 k) i p (SOME v1 :: SOME v2 :: r) eo errs =>
                     AP k i p (SOME (f2 v2 v1) :: r) eo errs
                 | AP (appf2 _ _) _ _ _ _ _ => Looped
                 | AP (returnTo i r k) i' p r' eo errs => AP k i p r eo errs
                 | AP (restoreEO eo k) i p r eo' errs => AP k i p r eo errs
                 | AP (listsym e f k) i p r eo errs =>
                     EV e i p r eo errs
                        (lpconj
                         (restoreEO eo $ listsym e f k)
                         (returnTo i r $ restoreEO eo $
                          addErr (sloc i) G.iFAIL $ poplist f $ k))
                        (poplist f k)
                 | AP (poplist f k) i p r eo [] => Looped
                 | AP (poplist f k) i p r eo (e :: errs) =>
                     AP k i p (poplistval f r) eo errs
                 | AP (lpcomp R k) i (p::ps) r eo errs =>
                     AP k i (comppred R p :: ps) r eo errs
                 | AP (lpcomp R k) i [] r eo errs => Looped
                 | AP (lpconj k fk) i (p1::p2::ps) r eo errs =>
                     let p = conjpred p2 p1 in
                       if p = lpBOT then AP fk i (p2::ps) r eo errs
                       else AP k i (p::ps) r eo errs
                 | AP (setlps ps k) i _ r eo errs => AP k i ps r eo errs
                 | Result r => Result r
                 | Looped => Looped)
End

Definition peg_exec_def[nocompute]:
  ispeg_exec (G:('atok,'bnt,'cvalue,'err)ispeg) e i p r eo errs k fk =
    case coreloop G (EV e i p r eo errs k fk) of
        SOME r => r
      | NONE => Looped
End

Definition applykont_def[nocompute]:
  applykont G k i p r eo errs =
  case coreloop G (AP k i p r eo errs) of
    SOME r => r
  | NONE => Looped
End

Theorem coreloop_result[simp]:
  coreloop G (Result x) = SOME (Result x)
Proof
  simp[coreloop_def, Once whileTheory.OWHILE_THM]
QED

Theorem coreloop_Looped[simp]:
  coreloop G Looped = NONE
Proof
  simp[coreloop_def, whileTheory.OWHILE_EQ_NONE] >> Induct >>
  simp[arithmeticTheory.FUNPOW]
QED

Theorem coreloop_LET[local]:
  coreloop G (LET f x) = LET (coreloop G o f) x
Proof
  simp[]
QED

Theorem option_case_LET[local]:
  option_CASE (LET f x) Looped sf =
  LET (option_CASE o f) x Looped sf
Proof
  REWRITE_TAC[combinTheory.GEN_LET_RAND]
QED

Theorem LET_RATOR[local]:
  LET f x Looped = LET (flip f Looped) x ∧
  LET g y (λr: (α,β,γ,δ)evalcase. r) = LET (flip g (λr. r)) y
Proof
  simp[]
QED

fun inst_thm def (qs,ths) =
    def |> SIMP_RULE (srw_ss()) [Once whileTheory.OWHILE_THM, coreloop_def]
        |> SPEC_ALL
        |> Q.INST qs
        |> SIMP_RULE (srw_ss()) []
        |> SIMP_RULE bool_ss (GSYM peg_exec_def :: GSYM coreloop_def ::
                              GSYM applykont_def :: coreloop_result ::
                              coreloop_LET :: combinTheory.o_ABS_R ::
                              option_case_LET :: LET_RATOR ::
                              combinTheory.C_ABS_L ::
                              optionTheory.option_case_def :: ths)

val peg_exec_thm = inst_thm peg_exec_def

val option_case_COND = prove(
  ``option_CASE (if P then Q else R) n s =
    if P then option_CASE Q n s else option_CASE R n s``,
  SRW_TAC [][]);


val better_peg_execs =
    map peg_exec_thm [([`e` |-> `empty v`], []),
                      ([`e` |-> `tok P f R`, `i` |-> `[]`], []),
                      ([`e` |-> `tok P f R`, `i` |-> `(tk,Locs l1 l2)::xs`],
                       [Once COND_RAND, option_case_COND]),
                      ([`e` |-> `any f`, `i` |-> `[]`], []),
                      ([`e` |-> `any f`, `i` |-> `x::xs`], []),
                      ([`e` |-> `seq e1 e2 sf`], []),
                      ([`e` |-> `choice e1 e2 cf`], []),
                      ([`e` |-> `not e v`], []),
                      ([`e` |-> `rpt e lf`], []),
                      ([‘e’ |-> ‘error err’], [])]

Theorem ispeg_nt_thm =
  peg_exec_thm ([`e` |-> `nt n nfn R`], [Once COND_RAND, option_case_COND])
  |> SIMP_RULE (srw_ss()) []

val better_apply =
    map (SIMP_RULE (srw_ss()) [] o inst_thm applykont_def)
        [([`k` |-> `ksym e k fk`], []),
         ([`k` |-> `appf1 f k`, `r` |-> `SOME v::r`], []),
         ([`k` |-> `appf2 f k`, `r` |-> `SOME v1::SOME v2::r`], []),
         ([`k` |-> `returnTo i' r' k`], []),
         ([‘k’ |-> ‘addErr l e k’], []),
         ([‘k’ |-> ‘dropErr k’, ‘errs’ |-> ‘[]’], []),
         ([‘k’ |-> ‘dropErr k’, ‘errs’ |-> ‘e::errs’], []),
         ([‘k’ |-> ‘cmpErrs k’, ‘errs’ |-> ‘(l1,er1)::(l2,er2)::errs’], []),
         ([`k` |-> `done`, ‘r’ |-> ‘[]’], []),
         ([`k` |-> `done`, ‘r’ |-> ‘NONE::rs’], []),
         ([`k` |-> `done`, ‘r’ |-> ‘SOME rv::rs’, ‘p’ |-> ‘[]’], []),
         ([`k` |-> `done`, ‘r’ |-> ‘SOME rv::rs’, ‘p’ |-> ‘p1::ps’], []),
         ([`k` |-> `failed`, ‘errs’ |-> ‘[]’], []),
         ([`k` |-> `failed`, ‘errs’ |-> ‘(l,e)::errs’], []),
         ([`k` |-> `poplist f k`, ‘errs’ |-> ‘[]’], []),
         ([`k` |-> `poplist f k`, ‘errs’ |-> ‘le::errs’], []),
         ([`k` |-> `listsym e f k`], []),
         ([‘k’ |-> ‘restoreEO eo0 k’], []),
         ([‘k’ |-> ‘cmpEO eo0 k’, ‘errs’ |-> ‘(l,err)::errs’], []),
         ([‘k’ |-> ‘lpconj k1 k2’, ‘p’ |-> ‘p1::p2::ps’],
          [option_case_COND, Once COND_RAND]),
         ([‘k’ |-> ‘lpcomp R k’, ‘p’ |-> ‘[]’], []),
         ([‘k’ |-> ‘lpcomp R k’, ‘p’ |-> ‘p1::ps’], []),
         ([‘k’ |-> ‘setlps ps k’], [])
         ]

Theorem peg_nt_thm =
  peg_exec_thm ([`e` |-> `nt n nfn R`], [Once COND_RAND, option_case_COND])
  |> SIMP_RULE (srw_ss()) []

Theorem peg_exec_thm[compute] = LIST_CONJ better_peg_execs

Theorem applykont_thm[compute] = LIST_CONJ better_apply


Theorem OME_NONE[local,simp]:
  OME NONE eo = eo ∧ OME eo NONE = eo
Proof
  Cases_on ‘eo’ >> simp[optmax_def]
QED

Theorem OME_ASSOC[local,simp]:
  OME eo1 (OME eo2 eo3) = OME (OME eo1 eo2) eo3
Proof
  map_every Cases_on [‘eo1’, ‘eo2’, ‘eo3’] >> simp[optmax_def] >>
  rename [‘MAXerr e1 (MAXerr e2 e3)’] >>
  map_every Cases_on [‘e1’, ‘e2’, ‘e3’] >> rw[MAXerr_def] >>
  metis_tac[locsle_total,locsle_TRANS]
QED

Theorem MAXerr_id[simp]:
  MAXerr x x = x
Proof
  Cases_on ‘x’ >> simp[MAXerr_def]
QED

Theorem FORALL_locs:
  (∀ls. P ls) ⇔ ∀l1 l2. P (Locs l1 l2)
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >> Cases_on ‘ls’  >> simp[]
QED

Theorem poplist_aux[simp,local]:
  ∀vs A. poplist_aux A (MAP SOME vs ++ [NONE] ++ stk) = (REVERSE vs ++ A, stk)
Proof
  Induct >> simp[poplist_aux_def]
QED

Theorem poplistval_correct[simp]:
  poplistval f (MAP SOME vs ++ NONE :: stk) =
  SOME (f (REVERSE vs)) :: stk
Proof
  simp[poplistval_def]
QED

Theorem exec_correct0[local]:
  (∀i e r.
     ispeg_eval G (i,e) r ⇒
     (∀j v eo eo0 k fk stk errs p ps.
        r = Success j v eo p ⇒
        ispeg_exec G e i ps stk eo0 errs k fk =
        applykont G k j (p::ps) (SOME v :: stk) (OME eo0 eo) errs) ∧
     (∀k fk stk eo errs l err ps.
        r = Failure l err ⇒
        ispeg_exec G e i ps stk eo errs k fk =
        applykont G fk i ps stk (OME eo (SOME (l,err))) ((l,err)::errs))) ∧
  (∀p0 i e j vlist errp.
     ispeg_eval_list G p0 (i,e) (j,vlist,errp) ⇒
     ∀vs f k stk eo err p errs ps.
       errp = (err,p) ⇒
       ispeg_exec G e i (p0::ps) (MAP SOME vs ++ (NONE::stk))
                eo
                errs
                (lpconj (restoreEO eo $ listsym e f k)
                 (returnTo i (MAP SOME vs ++ (NONE::stk)) $ restoreEO eo $
                  addErr (sloc i) G.iFAIL $ poplist f $ k))
                (poplist f k) =
       applykont G k j (p::ps) (SOME (f (REVERSE vs ++ vlist)) :: stk)
                 (OME eo (SOME err))
                 errs)
Proof
  ho_match_mp_tac ispeg_eval_strongind' >> rpt conj_tac >>
  simp[peg_exec_thm, peg_nt_thm, applykont_thm, FORALL_result, AllCaseEqs(),
       arithmeticTheory.ADD1, MAXerr_def, pairTheory.FORALL_PROD,
       FORALL_locs]
  >- ((* locsle comparison (choice has both branches fail) *)
      rw[optmax_def, MAXerr_def] >>
      simp[Excl "OME_ASSOC", GSYM OME_ASSOC, optmax_def, MAXerr_def])
  >- ((* rpt *)
      rpt strip_tac >> first_x_assum $ qspec_then ‘[]’ mp_tac >> simp[])
  >- ((* rpt - some elements succeed *)
      rpt strip_tac >> rename [‘SOME v::(MAP SOME vs ++ NONE::rest)’] >>
      first_x_assum $ qspec_then ‘v::vs’ mp_tac >> simp[] >>
      REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND])
QED

Theorem exec_correct =
  exec_correct0 |> SIMP_RULE (srw_ss() ++ DNF_ss) []

Theorem pegexec_succeeds =
  exec_correct
    |> CONJUNCTS |> hd |> SPEC_ALL
    |> Q.INST [`k` |-> `done`, `fk` |-> `failed`, `stk` |-> `[]`,
               ‘errs’ |-> ‘[]’, ‘ps’ |-> ‘[]’]
    |> SIMP_RULE (srw_ss()) [applykont_thm]

Theorem pegexec_fails =
  exec_correct |> CONJUNCTS |> tl |> hd |> SPEC_ALL
               |> Q.INST [`k` |-> `done`, `fk` |-> `failed`,
                          `stk` |-> `[]`, ‘errs’ |-> ‘[]’, ‘ps’ |-> ‘[]’]
               |> SIMP_RULE (srw_ss()) [applykont_thm]

val pair_CASES = pairTheory.pair_CASES
val option_CASES = optionTheory.option_nchotomy
val list_CASES = listTheory.list_CASES

Theorem ispegexec:
  ispeg_eval G (s,e) r ⇒ ispeg_exec G e s [] [] NONE [] done failed = Result r
Proof
  strip_tac >>
  Cases_on ‘r’ >> (drule pegexec_succeeds ORELSE drule pegexec_fails) >>
  simp[]
QED

Theorem ispeg_eval_executed:
  wfG G ∧ e ∈ Gexprs G ⇒
    (ispeg_eval G (s,e) r ⇔
       ispeg_exec G e s [] [] NONE [] done failed = Result r)
Proof
  strip_tac >> eq_tac >- simp[ispegexec] >>
  strip_tac >>
  ‘∃r'. ispeg_eval G (s,e) r'’ by metis_tac[ispeg_eval_total] >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  simp[] >> first_x_assum (assume_tac o MATCH_MP ispegexec) >> fs[]
QED

Definition destResult_def[simp]: destResult (Result r) = r
End

Definition ispegparse_def:
  ispegparse G s =
    if wfG G then
      case destResult (ispeg_exec G G.start s [] [] NONE [] done failed) of
        Success s v eo p => SOME (s,v,eo,p)
      | _ => NONE
    else NONE
End

Theorem ispegparse_eq_SOME:
  ispegparse G s = SOME (s', v, eo, p) ⇔
  wfG G ∧ ispeg_eval G (s,G.start) (Success s' v eo p)
Proof
  Tactical.REVERSE (Cases_on `wfG G`) >- simp[ispegparse_def] >>
  `∃r. ispeg_eval G (s,G.start) r`
    by metis_tac [ispeg_eval_total, start_IN_Gexprs] >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  simp[] >>
  reverse (Cases_on ‘r’)
  >- (rw[ispegparse_def] >> drule pegexec_fails >> simp[]) >>
  rw[ispegparse_def] >> drule pegexec_succeeds >> simp[] >> metis_tac[]
QED

Theorem pegparse_eq_NONE:
  ispegparse G s = NONE ⇔ ¬wfG G ∨ ∃l e. ispeg_eval G (s,G.start) (Failure l e)
Proof
  Cases_on `wfG G` >> simp[ispegparse_def] >>
  `∃r. ispeg_eval G (s,G.start) r`
    by metis_tac [ispeg_eval_total, start_IN_Gexprs] >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  simp[] >> reverse (Cases_on ‘r’) >> simp[]
  >- (drule pegexec_fails >> simp[]) >>
  drule pegexec_succeeds >> simp[]
QED

Theorem ispeg_exec_total:
  wfG G ==> ∃r. ispeg_exec G G.start i [] [] NONE [] done failed = Result r
Proof
  strip_tac >>
  ‘∃pr. ispeg_eval G (i, G.start) pr’
    by simp[ispeg_eval_total,start_IN_Gexprs] >>
  pop_assum mp_tac >> simp[ispeg_eval_executed, start_IN_Gexprs]
QED

(*
   |- wfG G ⇒
      ∃r.
        coreloop G (pegexec$EV G.start i [] NONE [] done failed) = SOME (Result r)
*)
Theorem coreloop_total =
  ispeg_exec_total |> SIMP_RULE (srw_ss()) [peg_exec_def, AllCaseEqs()]

val _ = app
        (fn s => ignore (remove_ovl_mapping s {Thy = "ispegexec", Name = s}))
        ["AP", "EV"]

val _ = export_theory()
