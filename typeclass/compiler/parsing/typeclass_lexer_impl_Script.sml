(*
  Definition of the lexer: code for consuming tokens until a top-level
  semicolon is found (semicolons can be hidden in `let`-`in`-`end` blocks,
  structures, signatures, and between parentheses).

  TODO: update this description if it is incorrect.
*)

open preamble tokensTheory locationTheory

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "pure_lexer_impl";
val _ = set_grammar_ancestry ["misc", "tokens", "ASCIInumbers", "location"]

(* val tac =
 full_simp_tac (srw_ss()) [char_le_def, char_lt_def] >>
 Cases_on `t` >>
 rw [get_token_def, processIdent_def, isAlphaNum_def, isAlpha_def, isDigit_def,
     isLower_def, isUpper_def];*)

Datatype:
  symbol = StringS string
         | CharS char
         | NumberS int
         | WordS num
         | LongS string (* identifiers with a . in them *)
         | FFIS string
         | OtherS string
         | ErrorS
End

(* helper functions *)
Definition mkCharS_def:
  (mkCharS (StringS s) = if LENGTH s = 1 then CharS (HD s)
                         else ErrorS) /\
  (mkCharS _ = ErrorS)
End

Definition read_while_def:
  (read_while P "" s = (IMPLODE (REVERSE s),"")) /\
  (read_while P (STRING c cs) s =
     if P c then read_while P cs (c :: s)
            else (IMPLODE (REVERSE s),STRING c cs))
End

Theorem read_while_thm:
   ∀cs s cs' s'.
       (read_while P cs s = (s',cs')) ⇒ STRLEN cs' <= STRLEN cs
Proof
  Induct THEN SRW_TAC [][read_while_def] THEN SRW_TAC [][] THEN
  RES_TAC THEN FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] THEN DECIDE_TAC
QED

Definition is_single_char_symbol_def:
  is_single_char_symbol c = MEM c "()[]{},;"
End

Definition isSymbol_def:
  isSymbol c = MEM c (CHR 96 (* backquote *) :: "!%&$#+-/:<=>?@\\~^|*")
End

Definition isAlphaNumPrime_def:
  isAlphaNumPrime c <=> isAlphaNum c \/ (c = #"'") \/ (c = #"_")
End

Definition next_loc_def:
  next_loc n (POSN r c) = POSN r (c+n) ∧
  next_loc n x = x
End

Definition next_line_def:
  next_line (POSN r c) = POSN (r+1) 1 ∧
  next_line x = x
End

Definition read_string_def:
  read_string str s (loc:locn) =
    if str = "" then (ErrorS, loc, "") else
    if HD str = #"\"" then (StringS s, loc, TL str) else
    if HD str = #"\n" then (ErrorS, next_line loc, TL str) else
    if HD str <> #"\\" then
      read_string (TL str) (s ++ [HD str]) (next_loc 1 loc)
    else
      case TL str of
      | #"\\"::cs => read_string cs (s ++ "\\") (next_loc 2 loc)
      | #"\""::cs => read_string cs (s ++ "\"") (next_loc 2 loc)
      | #"n"::cs => read_string cs (s ++ "\n") (next_loc 2 loc)
      | #"t"::cs => read_string cs (s ++ "\t") (next_loc 2 loc)
      | _ => (ErrorS, loc, TL str)
Termination
  WF_REL_TAC `measure (LENGTH o FST)` THEN REPEAT STRIP_TAC
  THEN Cases_on `str` THEN FULL_SIMP_TAC (srw_ss()) [] THEN DECIDE_TAC
End

Theorem read_string_thm:
  ∀s t l l' x1 x2. (read_string s t l = (x1, l', x2)) ⇒
                   (LENGTH x2 <= LENGTH s + LENGTH t)
Proof
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ HO_MATCH_MP_TAC (fetch "-" "read_string_ind")
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [read_string_def]
  \\ Cases_on `s` \\ SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [LENGTH] \\ RES_TAC \\ TRY DECIDE_TAC
  \\ SRW_TAC [] [LENGTH] \\ Cases_on `t'`
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ CCONTR_TAC
  \\ Q.PAT_X_ASSUM `(x1, l', x2) = xxx` MP_TAC
  \\ SIMP_TAC std_ss [] \\ SRW_TAC [] []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ TRY DECIDE_TAC \\ CCONTR_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC
QED

Definition skip_nested_comment_def:
  (skip_nested_comment "" d _ = NONE) /\
  (skip_nested_comment [x] d _ = NONE) /\
  (skip_nested_comment (x::y::xs) d loc =
    if [x;y] = "{-" then
      skip_nested_comment xs (d+1:num) (next_loc 2 loc)
    else if [x;y] = "-}" then
      (if d = 0 then SOME (xs, next_loc 2 loc)
       else skip_nested_comment xs (d-1) (next_loc 2 loc))
    else if ORD x = 10 then
      skip_nested_comment (y::xs) d (next_line loc)
    else skip_nested_comment (y::xs) d (next_loc 1 loc))
End

Theorem skip_nested_comment_thm:
   ∀xs d l l' str. skip_nested_comment xs d l = SOME (str, l') ⇒
                   LENGTH str ≤ LENGTH xs
Proof
  ho_match_mp_tac skip_nested_comment_ind >> simp[skip_nested_comment_def] >>
  rw[] >> gvs[]
QED

Definition skip_eol_comment_def:
  skip_eol_comment "" l = SOME ("", l) ∧
  skip_eol_comment (c::cs) l =
  if c = #"\n" then SOME (cs, next_line l)
  else skip_eol_comment cs (next_loc 1 l)
End

Theorem skip_eol_comment_thm:
  ∀cs l cs' l'. skip_eol_comment cs l = SOME (cs', l') ⇒ LENGTH cs' ≤ LENGTH cs
Proof
  Induct >>
  simp[skip_eol_comment_def, AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM] >>
  rw[] >> first_x_assum drule >> simp[]
QED

Definition unhex_alt_def:
  unhex_alt x = (if isHexDigit x then UNHEX x else 0n)
End

Definition num_from_dec_string_alt_def:
  num_from_dec_string_alt = s2n 10 unhex_alt
End
Definition num_from_hex_string_alt_def:
  num_from_hex_string_alt = s2n 16 unhex_alt
End

Definition read_FFIcall_def:
  (read_FFIcall "" acc loc = (ErrorS, loc, "")) ∧
  (read_FFIcall (c::s0) acc loc =
      if c = #")" then
        (FFIS (REVERSE acc), next_loc 2 loc, s0)
      else if c = #"\n" then (ErrorS, loc, s0)
      else if isSpace c then
        read_FFIcall s0 acc (next_loc 1 loc)
      else
        read_FFIcall s0 (c::acc) (next_loc 1 loc))
End

Theorem read_FFIcall_reduces_input:
   ∀s0 a l0 t l s.
     read_FFIcall s0 a l0 = (t, l, s) ⇒ LENGTH s < LENGTH s0 + 1
Proof
  Induct >> dsimp[read_FFIcall_def, bool_case_eq] >> rw[] >>
  qpat_x_assum `_ = _` (assume_tac o SYM) >> res_tac >> simp[]
QED

Definition next_sym_alt_def:
  (next_sym_alt "" _ = NONE) /\
  (next_sym_alt (c::str) loc =
     if c = #"\n" then (* skip new line *)
        next_sym_alt str (next_line loc)
     else if isSpace c then (* skip blank space *)
       next_sym_alt str (next_loc 1 loc)
     else if isDigit c then (* read number *)
       if str ≠ "" ∧ c = #"0" ∧ HD str = #"w" then
         if TL str = "" then SOME (ErrorS, Locs loc loc, "")
         else if isDigit (HD (TL str)) then
           let (n,rest) = read_while isDigit (TL str) [] in
             SOME (WordS (num_from_dec_string_alt n),
                   Locs loc (next_loc (LENGTH n + 1) loc),
                   rest)
         else if HD(TL str) = #"x" then
           let (n,rest) = read_while isHexDigit (TL (TL str)) [] in
             SOME (WordS (num_from_hex_string_alt n),
                   Locs loc (next_loc (LENGTH n + 2) loc),
                   rest)
         else SOME (ErrorS, Locs loc loc, TL str)
       else
         if str ≠ "" ∧ c = #"0" ∧ HD str = #"x" then
           let (n,rest) = read_while isHexDigit (TL str) [] in
             SOME (NumberS (& num_from_hex_string_alt n),
                   Locs loc (next_loc (LENGTH n) loc),
                   rest)
         else
           let (n,rest) = read_while isDigit str [] in
             SOME (NumberS (&(num_from_dec_string_alt (c::n))),
                   Locs loc (next_loc (LENGTH n) loc),
                   rest)
     else if c = #"~" /\ str <> "" /\ isDigit (HD str) then
       (* read negative number *)
       let (n,rest) = read_while isDigit str [] in
         SOME (NumberS (0- &(num_from_dec_string_alt n)),
               Locs loc (next_loc (LENGTH n) loc),
               rest)
     else if c = #"'" then (* read type variable *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         SOME (OtherS n,
               Locs loc (next_loc (LENGTH n - 1) loc),
               rest)
     else if c = #"\"" then (* read string *)
       let (t, loc', rest) = read_string str "" (next_loc 1 loc) in
         SOME (t, Locs loc loc', rest)
     else if c = #"`" then SOME (OtherS "`", Locs loc loc, str)
     else if isPREFIX "#\"" (c::str) then
       let (t, loc', rest) = read_string (TL str) "" (next_loc 2 loc) in
         SOME (mkCharS t, Locs loc loc', rest)
     else if isPREFIX "#(" (c::str) then
       let (t, loc', rest) =
             read_FFIcall (TL str) "" (next_loc 2 loc)
       in
         SOME (t, Locs loc loc', rest)
     else if isPREFIX "{-" (c::str) then
       case skip_nested_comment (TL str) (0:num) (next_loc 2 loc) of
       | NONE => SOME (ErrorS, Locs loc (next_loc 2 loc), "")
       | SOME (rest, loc') => next_sym_alt rest loc'
     else if isPREFIX "--" (c::str) ∧ (2 ≤ LENGTH str ⇒ ¬isPunct (EL 1 str))
     then
       case skip_eol_comment (TL str) (next_loc 2 loc) of
         NONE => SOME (ErrorS, Locs loc (next_loc 2 loc), "")
       | SOME (rest, loc') => next_sym_alt rest loc'
     else if is_single_char_symbol c then (* single character tokens, i.e. delimiters *)
       SOME (OtherS [c], Locs loc loc, str)
     else if isSymbol c then
       let (n,rest) = read_while isSymbol str [c] in
         SOME (OtherS n,
               Locs loc (next_loc (LENGTH n - 1) loc),
               rest)
     else if isAlpha c then (* read identifier *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         case rest of
              #"."::rest' =>
                (case rest' of
                      c'::rest' =>
                        if isAlpha c' then
                          let (n', rest'') = read_while isAlphaNumPrime rest' [c'] in
                            SOME (LongS (n ++ "." ++ n'),
                                  Locs loc
                                       (next_loc (LENGTH n + LENGTH n') loc),
                                  rest'')
                        else if isSymbol c' then
                          let (n', rest'') = read_while isSymbol rest' [c'] in
                            SOME (LongS (n ++ "." ++ n'),
                                  Locs loc
                                       (next_loc (LENGTH n + LENGTH n') loc),
                                  rest'')
                        else
                          SOME (ErrorS,
                                Locs loc (next_loc (LENGTH n) loc),
                                rest')
                    | "" => SOME (ErrorS,
                                  Locs loc (next_loc (LENGTH n) loc),
                                  []))
            | _ => SOME (OtherS n,
                         Locs loc (next_loc (LENGTH n - 1) loc),
                         rest)
     else if c = #"_" then SOME (OtherS "_", Locs loc loc, str)
     else (* input not recognised *)
       SOME (ErrorS, Locs loc loc, str))
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ >> rpt strip_tac >> simp[] >~
  [‘skip_nested_comment’]
  >- (drule skip_nested_comment_thm >> rename [‘TL str’] >> Cases_on ‘str’ >>
      gs[]) >~
  [‘skip_eol_comment’]
  >- (drule skip_eol_comment_thm >> rename [‘TL str’] >> Cases_on ‘str’ >>
      gs[])
End

Triviality EVERY_isDigit_imp:
  EVERY isDigit x ⇒ MAP UNHEX x = MAP unhex_alt x
Proof
  rw[]>>match_mp_tac LIST_EQ>>
  fs[EL_MAP,EVERY_EL,unhex_alt_def,isDigit_def,isHexDigit_def]
QED

Triviality toNum_rw:
  ∀x. EVERY isDigit x ⇒ toNum x = num_from_dec_string_alt x
Proof
  rw[ASCIInumbersTheory.s2n_def,ASCIInumbersTheory.num_from_dec_string_def,
     num_from_dec_string_alt_def]>>
  AP_TERM_TAC>>
  match_mp_tac EVERY_isDigit_imp>>
  metis_tac[rich_listTheory.EVERY_REVERSE]
QED

Triviality EVERY_isHexDigit_imp:
  EVERY isHexDigit x ⇒ MAP UNHEX x = MAP unhex_alt x
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[EL_MAP,EVERY_EL,unhex_alt_def]
QED

Triviality num_from_hex_string_rw:
  ∀x. EVERY isHexDigit x ⇒ num_from_hex_string x = num_from_hex_string_alt x
Proof
  rw[ASCIInumbersTheory.s2n_def,ASCIInumbersTheory.num_from_hex_string_def,
     num_from_hex_string_alt_def]>>
  AP_TERM_TAC>>
  match_mp_tac EVERY_isHexDigit_imp>>
  metis_tac[rich_listTheory.EVERY_REVERSE]
QED

Triviality EVERY_IMPLODE:
  ∀ls P. EVERY P (IMPLODE ls) ⇔ EVERY P ls
Proof Induct>>fs[]
QED

Triviality read_while_P_lem:
  ∀ ls rest P x y.
    EVERY P rest ∧ read_while P ls rest = (x,y) ⇒ EVERY P x
Proof
  Induct>>fs[read_while_def]>>rw[]>>
  fs[EVERY_IMPLODE,rich_listTheory.EVERY_REVERSE]>>
  first_assum match_mp_tac>>fs[]>>
  qexists_tac`STRING h rest`>>fs[]
QED

Theorem read_while_P[local]:
  ∀ls P x y. read_while P ls "" = (x,y) ⇒ EVERY P x
Proof
  rw[]>>ho_match_mp_tac read_while_P_lem>>
  MAP_EVERY qexists_tac [`ls`,`""`,`y`]>>fs[]
QED

Theorem next_sym_alt_LESS:
  ∀input0 locn input.
    next_sym_alt input0 locn = SOME (sym, locn', input) ⇒
    LENGTH input < LENGTH input0
Proof
  recInduct next_sym_alt_ind >> simp[next_sym_alt_def] >> rw[] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >> gvs[AllCaseEqs()] >>~-
  ([‘TL (TL str)’, ‘read_while’],
   Cases_on ‘str’ >> gvs[] >> rename [‘TL str0’] >>
   Cases_on ‘str0’ >> gvs[] >> drule read_while_thm >> simp[]) >>~-
  ([‘TL str’, ‘read_while’],
   Cases_on ‘str’ >> gvs[] >> drule read_while_thm >> simp[]) >>~-
  ([‘read_while’], rpt $ dxrule read_while_thm >> simp[]) >~
  [‘skip_nested_comment (TL str) _ _ = _’]
  >- (drule skip_nested_comment_thm >> Cases_on ‘str’ >> gvs[]) >~
  [‘read_string’, ‘TL str’]
  >- (Cases_on ‘str’ >> gvs[] >> drule read_string_thm >> simp[]) >~
  [‘read_string’]
  >- (drule read_string_thm >> simp[]) >~
  [‘read_FFIcall (TL str)’]
  >- (Cases_on ‘str’ >> gs[] >> drule read_FFIcall_reduces_input >> simp[]) >~
  [‘skip_eol_comment’]
  >- (drule skip_eol_comment_thm >> Cases_on ‘str’ >> gvs[]) >>
  rename [‘TL str’] >> Cases_on ‘str’ >> gs[]
QED

(* lex_until_toplevel_semicolon *)
Definition processIdent_def:
  processIdent s =
    case s of
       | "" => LexErrorT
       | c::s =>
           if isAlpha c then
             AlphaT (c::s)
           else
             SymbolT (c::s)
End

Definition get_token_def[nocompute]:
  get_token s =
    if s = "(" then LparT else
    if s = ")" then RparT else
    if s = "," then CommaT else
    if s = ";" then SemicolonT else
    if s = "=" then EqualsT else
    if s = "[" then LbrackT else
    if s = "]" then RbrackT else
    if s = "{" then LbraceT else
    if s = "}" then RbraceT else
    if s = "|" then BarT else
    if s = "_" then UnderbarT else
    if s = "case" then CaseT else
    if s = "else" then ElseT else
    if s = "exception" then ExceptionT else
    if s = "if" then IfT else
    if s = "in" then InT else
    if s = "include" then IncludeT else
    if s = "let" then LetT else
    if s = "of" then OfT else
    if s = "then" then ThenT else
    if s = "type" then TypeT else
    if s = "where" then WhereT else
    processIdent s
End

Definition token_of_sym_def:
  token_of_sym s =
    case s of
    | ErrorS    => LexErrorT
    | StringS s => StringT s
    | CharS c => CharT c
    | NumberS i => IntT i
    | WordS n => WordT n
    | LongS s => let (s1,s2) = SPLITP (\x. x = #".") s in
                   LongidT s1 (case s2 of "" => "" | (c::cs) => cs)
    | FFIS s => FFIT s
    | OtherS s  => get_token s
End

Definition next_token_def:
  next_token input loc =
    case next_sym_alt input loc of
    | NONE => NONE
    | SOME (sym, locs, rest_of_input) =>
        SOME (token_of_sym sym, locs, rest_of_input)
End

Theorem next_token_LESS:
   ∀s l l' rest input. (next_token input l = SOME (s, l', rest)) ⇒
                       LENGTH rest < LENGTH input
Proof
  rpt gen_tac >> Cases_on ‘next_sym_alt input l’ >>
  simp[next_token_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >>
  drule next_sym_alt_LESS >> simp[]
QED

(* top-level lexer specification *)

Definition lexer_fun_aux_def:
  lexer_fun_aux input loc =
    case next_token input loc of
    | NONE => []
    | SOME (token, Locs loc' loc'', rest_of_input) =>
        (token, Locs loc' loc'') ::
            lexer_fun_aux rest_of_input (next_loc 1 loc'')
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ >> rw[] >> imp_res_tac next_token_LESS
End

Definition lexer_fun_def:
  lexer_fun input = lexer_fun_aux input (POSN 1 1)
End

val _ = export_theory();
