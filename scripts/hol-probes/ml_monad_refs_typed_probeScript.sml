(* Typed captures for the remaining ml_monadBase declarations (task 273): the
   monad combinators, the reference primitives and their characteristic
   equations, plus the fixed-array resize primitive. *)
load "preamble";
load "ml_monadBaseTheory";
open HolKernel Parse boolLib bossLib;
open preamble ml_monadBaseTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "ml_monadBase", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in ml_monadBase>\n");

val _ = emit "liftM_def_typed" "liftM_def";
val _ = emit "otherwise_def_typed" "otherwise_def";
val _ = emit "can_def_typed" "can_def";
val _ = emit "ref_bind_def_typed" "ref_bind_def";
val _ = emit "Mget_ref_def_typed" "Mget_ref_def";
val _ = emit "Mset_ref_def_typed" "Mset_ref_def";
val _ = emit "st_ex_bind_CONG_typed" "st_ex_bind_CONG";
val _ = emit "st_ex_ignore_bind_CONG_typed" "st_ex_ignore_bind_CONG";
val _ = emit "array_resize_def_typed" "array_resize_def";
val _ = emit "array_resize_eq_typed" "array_resize_eq";
val _ = emit "Marray_resize_def_typed" "Marray_resize_def";
val _ = emit "Mref_def_typed" "Mref_def";
val _ = emit "dref_def_typed" "dref_def";
val _ = emit "ref_assign_def_typed" "ref_assign_def";
val _ = emit "Mdref_aux_def_typed" "Mdref_aux_def";
val _ = emit "Mdref_def_typed" "Mdref_def";
val _ = emit "Mpop_ref_def_typed" "Mpop_ref_def";
val _ = emit "Mref_assign_aux_def_typed" "Mref_assign_aux_def";
val _ = emit "Mref_assign_def_typed" "Mref_assign_def";
val _ = emit "dref_first_typed" "dref_first";
val _ = emit "dref_cons_state_typed" "dref_cons_state";
val _ = emit "Mdref_eq_typed" "Mdref_eq";
val _ = emit "Mref_assign_aux_eq_typed" "Mref_assign_aux_eq";
val _ = emit "Mref_assign_eq_typed" "Mref_assign_eq";
