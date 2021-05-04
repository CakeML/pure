(* An itree-based semantics for CakeML *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open lem_pervasives_extraTheory libTheory namespaceTheory astTheory
     ffiTheory semanticPrimitivesTheory;
open io_treeTheory;

val _ = new_theory "cakeml_semantics"

Datatype:
  app_result = Rval v | Rraise v
End

Definition do_app_def:
  do_app s op vs = case (op, vs) of
      (ListAppend, [x1; x2]) => (
        case (v_to_list x1, v_to_list x2) of
          (SOME xs, SOME ys) => SOME (s, Rval (list_to_v (xs ++ ys)))
        | _ => NONE
      )
    | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        if (op = Divide ∨ op = Modulo) ∧ n2 = 0 then
          SOME (s, Rraise div_exn_v)
        else
          SOME (s, Rval (Litv (IntLit (opn_lookup op n1 n2))))
    | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        SOME (s, Rval (Boolv (opb_lookup op n1 n2)))
    | (Opw W8 op, [Litv (Word8 w1); Litv (Word8 w2)]) =>
        SOME (s, Rval (Litv (Word8 (opw8_lookup op w1 w2))))
    | (Opw W64 op, [Litv (Word64 w1); Litv (Word64 w2)]) =>
        SOME (s, Rval (Litv (Word64 (opw64_lookup op w1 w2))))
    | (FP_top t_op, [Litv (Word64 w1); Litv (Word64 w2); Litv (Word64 w3)]) =>
        SOME (s, Rval (Litv (Word64 (fp_top t_op w1 w2 w3))))
    | (FP_bop bop, [Litv (Word64 w1); Litv (Word64 w2)]) =>
        SOME (s,Rval (Litv (Word64 (fp_bop bop w1 w2))))
    | (FP_uop uop, [Litv (Word64 w)]) =>
        SOME (s,Rval (Litv (Word64 (fp_uop uop w))))
    | (FP_cmp cmp, [Litv (Word64 w1); Litv (Word64 w2)]) =>
        SOME (s,Rval (Boolv (fp_cmp cmp w1 w2)))
    | (Shift W8 op n, [Litv (Word8 w)]) =>
        SOME (s, Rval (Litv (Word8 (shift8_lookup op w n))))
    | (Shift W64 op n, [Litv (Word64 w)]) =>
        SOME (s, Rval (Litv (Word64 (shift64_lookup op w n))))
    | (Equality, [v1; v2]) =>
        (case do_eq v1 v2 of
            Eq_type_error => NONE
          | Eq_val b => SOME (s, Rval (Boolv b))
        )
    | (Opassign, [Loc lnum; v]) =>
        (case store_assign lnum (Refv v) s of
            SOME s' => SOME (s', Rval (Conv NONE []))
          | NONE => NONE
        )
    | (Opref, [v]) =>
        let (s',n) = (store_alloc (Refv v) s) in
          SOME (s', Rval (Loc n))
    | (Opderef, [Loc n]) =>
        (case store_lookup n s of
            SOME (Refv v) => SOME (s,Rval v)
          | _ => NONE
        )
    | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
        if n <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let (s',lnum) =
            (store_alloc (W8array (REPLICATE (Num (ABS (I n))) w)) s)
          in
            SOME (s', Rval (Loc lnum))
    | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                SOME (s, Rraise sub_exn_v)
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH ws then
                    SOME (s, Rraise sub_exn_v)
                  else
                    SOME (s, Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8sub_unsafe, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                NONE
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH ws then
                    NONE
                  else
                    SOME (s, Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8length, [Loc n]) =>
        (case store_lookup n s of
            SOME (W8array ws) =>
              SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aw8update, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              SOME (s, Rraise sub_exn_v)
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH ws then
                  SOME (s, Rraise sub_exn_v)
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (Aw8update_unsafe, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              NONE
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH ws then
                  NONE
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (WordFromInt W8, [Litv(IntLit i)]) =>
        SOME (s, Rval (Litv (Word8 (i2w i))))
    | (WordFromInt W64, [Litv(IntLit i)]) =>
        SOME (s, Rval (Litv (Word64 (i2w i))))
    | (WordToInt W8, [Litv (Word8 w)]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (WordToInt W64, [Litv (Word64 w)]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (CopyStrStr, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len)]) =>
        SOME (s,
        (case copy_array (EXPLODE str,off) len NONE of
          NONE => Rraise sub_exn_v
        | SOME cs => Rval (Litv(StrLit(IMPLODE(cs))))
        ))
    | (CopyStrAw8, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len);
                    Loc dst;Litv(IntLit dstoff)]) =>
        (case store_lookup dst s of
          SOME (W8array ws) =>
            (case copy_array (EXPLODE str,off) len (SOME(ws_to_chars ws,dstoff)) of
              NONE => SOME (s, Rraise sub_exn_v)
            | SOME cs =>
              (case store_assign dst (W8array (chars_to_ws cs)) s of
                SOME s' =>  SOME (s', Rval (Conv NONE []))
              | _ => NONE
              )
            )
        | _ => NONE
        )
    | (CopyAw8Str, [Loc src;Litv(IntLit off);Litv(IntLit len)]) =>
      (case store_lookup src s of
        SOME (W8array ws) =>
        SOME (s,
          (case copy_array (ws,off) len NONE of
            NONE => Rraise sub_exn_v
          | SOME ws => Rval (Litv(StrLit(IMPLODE(ws_to_chars ws))))
          ))
      | _ => NONE
      )
    | (CopyAw8Aw8, [Loc src;Litv(IntLit off);Litv(IntLit len);
                    Loc dst;Litv(IntLit dstoff)]) =>
      (case (store_lookup src s, store_lookup dst s) of
        (SOME (W8array ws), SOME (W8array ds)) =>
          (case copy_array (ws,off) len (SOME(ds,dstoff)) of
            NONE => SOME (s, Rraise sub_exn_v)
          | SOME ws =>
              (case store_assign dst (W8array ws) s of
                SOME s' => SOME (s', Rval (Conv NONE []))
              | _ => NONE
              )
          )
      | _ => NONE
      )
    | (Ord, [Litv (Char c)]) =>
          SOME (s, Rval (Litv(IntLit(int_of_num(ORD c)))))
    | (Chr, [Litv (IntLit i)]) =>
        SOME (s,
          (if (i <( 0 : int)) \/ (i >( 255 : int)) then
            Rraise chr_exn_v
          else
            Rval (Litv(Char(CHR(Num (ABS (I i))))))))
    | (Chopb op, [Litv (Char c1); Litv (Char c2)]) =>
        SOME (s, Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
    | (Implode, [v]) =>
          (case v_to_char_list v of
            SOME ls =>
              SOME (s, Rval (Litv (StrLit (IMPLODE ls))))
          | NONE => NONE
          )
    | (Explode, [v]) =>
          (case v of
            Litv (StrLit str) =>
              SOME (s, Rval (list_to_v (MAP (\ c .  Litv (Char c)) (EXPLODE str))))
          | _ => NONE
          )
    | (Strsub, [Litv (StrLit str); Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let n = (Num (ABS (I i))) in
            if n >= STRLEN str then
              SOME (s, Rraise sub_exn_v)
            else
              SOME (s, Rval (Litv (Char (EL n (EXPLODE str)))))
    | (Strlen, [Litv (StrLit str)]) =>
        SOME (s, Rval (Litv(IntLit(int_of_num(STRLEN str)))))
    | (Strcat, [v]) =>
        (case v_to_list v of
          SOME vs =>
            (case vs_to_string vs of
              SOME str =>
                SOME (s, Rval (Litv(StrLit str)))
            | _ => NONE
            )
        | _ => NONE
        )
    | (VfromList, [v]) =>
          (case v_to_list v of
              SOME vs =>
                SOME (s, Rval (Vectorv vs))
            | NONE => NONE
          )
    | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let n = (Num (ABS (I i))) in
            if n >= LENGTH vs then
              SOME (s, Rraise sub_exn_v)
            else
              SOME (s, Rval (EL n vs))
    | (Vlength, [Vectorv vs]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
    | (Aalloc, [Litv (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let (s',lnum) =
            (store_alloc (Varray (REPLICATE (Num (ABS (I n))) v)) s)
          in
            SOME (s', Rval (Loc lnum))
    | (AallocEmpty, [Conv NONE []]) =>
        let (s',lnum) = (store_alloc (Varray []) s) in
          SOME (s', Rval (Loc lnum))
    | (Asub, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                SOME (s, Rraise sub_exn_v)
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH vs then
                    SOME (s, Rraise sub_exn_v)
                  else
                    SOME (s, Rval (EL n vs))
          | _ => NONE
        )
    | (Asub_unsafe, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                NONE
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH vs then
                    NONE
                  else
                    SOME (s, Rval (EL n vs))
          | _ => NONE
        )
    | (Alength, [Loc n]) =>
        (case store_lookup n s of
            SOME (Varray ws) =>
              SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aupdate, [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              SOME (s, Rraise sub_exn_v)
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH vs then
                  SOME (s, Rraise sub_exn_v)
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (Aupdate_unsafe, [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              NONE
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH vs then
                  NONE
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (ConfigGC, [Litv (IntLit i); Litv (IntLit j)]) =>
        SOME (s, Rval (Conv NONE []))
    | (Env_id, [Env env (gen, id)]) => SOME (s,
            Rval (Conv NONE [nat_to_v gen; nat_to_v id]))
    | (Env_id, [Conv NONE [gen; id]]) => SOME (s,
            Rval (Conv NONE [gen; id]))
    | _ => NONE
End

Datatype:
  ctxt_frame = Craise
             | Chandle ((pat # exp) list)
             | Capp op (v list) (exp list)
             | Clog lop exp
             | Cif exp exp
             | Cmat_check ((pat # exp) list) v
             | Cmat ((pat # exp) list) v
             | Clet (varN option) exp
             | Ccon (((modN, conN) id) option) (v list) (exp list)
             | Ctannot ast_t
             | Clannot locs
End

Type "ctxt"[pp] = ``:ctxt_frame # v sem_env``;

Type "small_state"[pp] = ``:v sem_env # v store # exp_or_val # ctxt list``;

Datatype:
  estep_result = Estep small_state
               | Effi string (word8 list) (word8 list) num
                        (v sem_env) (v store) (ctxt list)
               | Edone
               | Etype_error
End

Definition push_def:
  push env s e c cs : estep_result = Estep (env, s, Exp e, (c,env)::cs)
End

(* This is value_def in stateLang *)
Definition return_def:
  return env s v c : estep_result = Estep (env, s, Val v, c)
End

Definition application_def:
  application op env s vs c : estep_result =
    case op of
      Opapp => (
        case do_opapp vs of
          SOME (env, e) => Estep (env, s, Exp e, c)
        | NONE => Etype_error)
    | FFI n => (
        case vs of
          [Litv (StrLit conf); Loc lnum] => (
            case store_lookup lnum s of
              SOME (W8array ws) =>
                Effi n (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env s c
            | NONE => Etype_error)
        | _ => Etype_error)
    | _ => (
        case do_app s op vs of
          SOME (s', Rraise v) => Estep (env, s', Val v, (Craise, env)::c)
        | SOME (s', Rval v)   => return env s' v c
        | NONE                => Etype_error)
End

(* This is return_def in stateLang *)
Definition continue_def:
  continue s v [] : estep_result = Edone ∧
  continue s v ((Craise, env)::cs) = (
    case cs of
      [] => Edone
    | (Chandle pes, env') :: c =>
        Estep (env, s, Val v, (Cmat_check pes v, env')::c)
    | _::c => Estep (env, s, Val v, (Craise, env)::c)) ∧
  continue s v ((Chandle pes, env)::c) = return env s v c ∧
  continue s v ((Capp op vs [], env) :: c) = application op env s (v::vs) c ∧
  continue s v ((Capp op vs (e::es), env) :: c) = push env s e (Capp op (v::vs) es) c ∧
  continue s v ((Clog l e, env) :: c) = (
    case do_log l v e of
      SOME (Exp e) => Estep (env, s, Exp e, c)
    | SOME (Val v) => return env s v c
    | NONE => Etype_error) ∧
  continue s v ((Cif e1 e2, env) :: c) = (
    case do_if v e1 e2 of
      SOME e => Estep (env, s, Exp e, c)
    | NONE => Etype_error) ∧
  continue s v ((Cmat_check pes err_v, env) :: c) = (
    if can_pmatch_all env.c s (MAP FST pes) v then
      Estep (env, s, Val v, (Cmat pes err_v, env)::c)
    else Etype_error) ∧
  continue s v ((Cmat [] err_v, env) :: c) =
    Estep (env, s, Val err_v, (Craise, env)::c) ∧
  continue s v ((Cmat ((p,e)::pes) err_v, env) :: c) = (
    if ALL_DISTINCT (pat_bindings p []) then (
      case pmatch env.c s p v [] of
        Match_type_error => Etype_error
      | No_match => Estep (env, s, Val v, (Cmat pes err_v, env)::c)
      | Match env' =>
          Estep (
            env with <| v := nsAppend (alist_to_ns env') env.v |>, s, Exp e, c))
    else Etype_error) ∧
  continue s v ((Clet n e, env) :: c) =
    Estep (env with <| v := nsOptBind n v env.v |>, s, Exp e, c) ∧
  continue s v ((Ccon n vs [], env) :: c) = (
    if do_con_check env.c n (LENGTH vs + 1n) then (
      case build_conv env.c n (v::vs) of
        NONE => Etype_error
      | SOME v => return env s v c)
    else Etype_error) ∧
  continue s v ((Ccon n vs (e::es), env) :: c) = (
    if do_con_check env.c n (LENGTH vs + 1n + 1n + LENGTH es) then
      push env s e (Ccon n (v::vs) es) c
    else Etype_error) ∧
  continue s v ((Ctannot t, env) :: c) = return env s v c ∧
  continue s v ((Clannot l, env) :: c) = return env s v c
End

Definition estep_def:
  estep (env, s, Val v, c) : estep_result = continue s v c ∧
  estep (env, s, Exp $ Lit l, c) = return env s (Litv l) c ∧
  estep (env, s, Exp $ Raise e, c) = push env s e Craise c ∧
  estep (env, s, Exp $ Handle e pes, c) = push env s e (Chandle pes) c ∧
  estep (env, s, Exp $ Con n es, c) = (
    if do_con_check env.c n (LENGTH es) then (
      case REVERSE es of
        [] => (
          case build_conv env.c n [] of
            NONE => Etype_error
          | SOME v => return env s v c)
      | e::es => push env s e (Ccon n [] es) c)
    else Etype_error) ∧
  estep (env, s, Exp $ Var n, c) = (
    case nsLookup env.v n of
      NONE => Etype_error
    | SOME v => return env s v c) ∧
  estep (env, s, Exp $ Fun n e, c) = return env s (Closure env n e) c ∧
  estep (env, s, Exp $ App op es, c) = (
    case REVERSE es of
      [] => application op env s [] c
    | (e::es) => push env s e (Capp op [] es) c) ∧
  estep (env, s, Exp $ Log l e1 e2, c) = push env s e1 (Clog l e2) c ∧
  estep (env, s, Exp $ If e1 e2 e3, c) = push env s e1 (Cif e2 e3) c ∧
  estep (env, s, Exp $ Mat e pes, c) = push env s e (Cmat_check pes bind_exn_v) c ∧
  estep (env, s, Exp $ Let n e1 e2, c) = push env s e1 (Clet n e2) c ∧
  estep (env, s, Exp $ Letrec funs e, c) = (
    if ¬ALL_DISTINCT (MAP FST funs) then Etype_error
    else Estep (env with <| v := build_rec_env funs env env.v |>, s, Exp e, c)) ∧
  estep (env, s, Exp $ Tannot e t, c) = push env s e (Ctannot t) c ∧
  estep (env, s, Exp $ Lannot e l, c) = push env s e (Clannot l) c
End

Definition is_halt_def:
  is_halt (Effi s ws1 ws2 n env st cs) = T ∧
  is_halt Edone = T ∧
  is_halt Etype_error = T ∧
  is_halt _ = F
End

Definition step_n_def:
  step_n 0 e = e ∧
  step_n (SUC n) (Estep st) = step_n n (estep st) ∧
  step_n _ e = e
End

Datatype:
  next_res = (* top-level observable results *)
           | Act string (word8 list) (word8 list)
                num (v sem_env) (v store) (ctxt list)
           | Ret
           | Div
           | Err
End

Definition step_until_halt_def:
  step_until_halt e =
    case some n. is_halt (step_n n e) of
      NONE => Div
    | SOME n =>
        case step_n n e of
          Effi s ws1 ws2 n env st cs => Act s ws1 ws2 n env st cs
        | Etype_error => Err
        | _ => Ret
End

Datatype:
  result = SilentDivergence
         | Termination
         | Error
         | FinalFFI ffi_outcome
End

Definition cml_io_unfold_err_def:
  cml_io_unfold_err f =
    io_unfold_err f
      ((λ(_,_,ws) r. LENGTH ws = LENGTH r),
      FinalFFI, FinalFFI FFI_failed)
End

Theorem cml_io_unfold_err:
  cml_io_unfold_err f seed =
    case f seed of
    | Ret' r   => Ret r
    | Vis' (s, ws1, ws2) g =>
        Vis (s, ws1, ws2)
          (λa. case a of
                  INL x => Ret $ FinalFFI x
                | INR y =>
                    if LENGTH ws2 = LENGTH y then cml_io_unfold_err f (g y)
                    else Ret $ FinalFFI FFI_failed)
Proof
  CASE_TAC >> gvs[cml_io_unfold_err_def] >>
  simp[Once io_unfold_err] >>
  PairCases_on `e` >> gvs[]
QED

Definition interp_def:
  interp e =
    cml_io_unfold_err
      (λe.
        case step_until_halt e of
        | Ret => Ret' Termination
        | Err => Ret' Error
        | Div => Ret' SilentDivergence
        | Act s ws1 ws2 n env st cs =>
            Vis' (s, ws1, ws2)
              (λr:word8 list.
                Estep (env, LUPDATE (W8array r) n st, Val $ Conv NONE [], cs)))
      e
End

val _ = export_theory();

