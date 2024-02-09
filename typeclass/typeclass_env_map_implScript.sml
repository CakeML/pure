(* concrete data structures for implementing
* instance map and type class map *)
open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;

open pairTheory optionTheory listTheory pred_setTheory finite_mapTheory
open mlmapTheory mlstringTheory typeclass_tcexpTheory

val _ = new_theory "typeclass_env_map_impl";

Datatype:
  classinfo_impl =
    <| super : mlstring list
     ; kind : Kind option
     ; methodsig : (cvname, PredType) mlmap$map
     ; minImp : minImplAST
     ; defaults : (cvname, tcexp) mlmap$map |>
End

Datatype:
  instinfo_impl =
    <| cstr : (mlstring # num) list (* class and type variable*)
     ; impl : (cvname, tcexp) mlmap$map |> (* function name and its expression *)
End

Type class_map_impl = ``:(mlstring, classinfo_impl) map``;
Type inst_map_impl = ``:(mlstring, (type # instinfo_impl) list) map``;

Definition to_class_map_def:
  to_class_map (m:class_map_impl) = FMAP_MAP2 (λ(k,x).
    <| super := x.super
     ; kind := x.kind
     ; methodsig := to_fmap x.methodsig
     ; minImp := x.minImp
     ; defaults := to_fmap x.defaults |>) (to_fmap m)
End

Definition to_inst_map_def:
  to_inst_map (m:inst_map_impl) =
    FMAP_MAP2 (λ(k1,l).
      MAP (λ(k2,x). (k2, <|cstr := x.cstr; impl := to_fmap x.impl|>)) l)
    (to_fmap m)
End

Definition lookup_inst_map_def:
  lookup_inst_map (m:inst_map_impl) cl ty =
    OPTION_BIND (lookup m cl) (λl. ALOOKUP l ty)
End

Definition add_instance_def:
  add_instance (inst_map:inst_map_impl) cl ty info =
    case lookup inst_map cl of
      | NONE => SOME $ insert inst_map cl [(ty,info)]
      | SOME l =>
        (case ALOOKUP l ty of
          | NONE => SOME $ insert inst_map cl ((ty,info)::l)
          | _ => NONE)
End

(*
Definition lookup_inst_map_type_pat_def:
  lookup_inst_map_type_pat (m:instinfo_impl) cl ty =
  (ARB:(type # instinfo_impl) list)
End
*)

val _ = export_theory();
