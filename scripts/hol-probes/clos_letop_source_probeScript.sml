(* Typed source declarations for closure let-operation cleanup. *)
load "clos_letopTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "var_list_typed" clos_letopTheory.var_list_def;
val _ = show "dest_op_typed" clos_letopTheory.dest_op_def;
val _ = show "let_op_sing_typed" clos_letopTheory.let_op_sing_def;
val _ = show "let_op_sing_eq_typed" clos_letopTheory.let_op_sing_eq;
val _ = show "compile_inc_typed" clos_letopTheory.compile_inc_def;
