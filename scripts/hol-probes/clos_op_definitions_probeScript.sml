(* Typed definitions for the executed closure smart-operation helpers. *)
load "clos_opTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print "="; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "dest_const_typed" clos_opTheory.dest_Const_def;
val _ = show "dest_constant_typed" clos_opTheory.dest_Constant_def;
val _ = show "dest_cons_typed" clos_opTheory.dest_Cons_def;
val _ = show "dest_elem_at_typed" clos_opTheory.dest_ElemAt_def;
val _ = show "dest_tag_eq_typed" clos_opTheory.dest_TagEq_def;
val _ = show "dest_len_eq_typed" clos_opTheory.dest_LenEq_def;
val _ = show "dest_tag_len_eq_typed" clos_opTheory.dest_TagLenEq_def;
val _ = show "dest_op_typed" clos_opTheory.dest_Op_def;
val _ = show "dest_op_nil_typed" clos_opTheory.dest_Op_Nil_def;
val _ = show "dest_op_consts_typed" clos_opTheory.dest_Op_Consts_def;
val _ = show "make_bool_typed" clos_opTheory.MakeBool_def;
val _ = show "make_int_typed" clos_opTheory.MakeInt_def;
val _ = show "int_op_typed" clos_opTheory.int_op_def;
val _ = show "cons_op_typed" clos_opTheory.cons_op_def;
val _ = show "is_var_typed" clos_opTheory.is_Var_def;
val _ = show "eq_direct_nil_typed" clos_opTheory.eq_direct_nil_def;
val _ = show "eq_direct_const_typed" clos_opTheory.eq_direct_const_def;
val _ = show "eq_direct_constant_typed" clos_opTheory.eq_direct_constant_def;
val _ = show "eq_direct_typed" clos_opTheory.eq_direct_def;
val _ = show "dont_lift_typed" clos_opTheory.dont_lift_def;
val _ = show "lift_exps_typed" clos_opTheory.lift_exps_def;
val _ = show "eq_pure_list_typed" clos_opTheory.eq_pure_list_def;
val _ = show "conj_list_typed" clos_opTheory.ConjList_def;
val _ = show "eq_pure_typed" clos_opTheory.eq_pure_def;
val _ = show "eq_any_typed" clos_opTheory.eq_any_def;
val _ = show "eq_op_typed" clos_opTheory.eq_op_def;
val _ = show "smart_prime_typed" clos_opTheory.SmartOp'_def;
val _ = show "smart_typed" clos_opTheory.SmartOp_def;
