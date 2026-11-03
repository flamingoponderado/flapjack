(* Typed source definitions for De Bruijn variable sets. *)
load "db_varsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "mk_union_typed=" db_varsTheory.mk_Union_def;
val _ = show "list_union_typed=" db_varsTheory.list_mk_Union_def;
val _ = show "db_to_set_acc_typed=" db_varsTheory.db_to_set_acc_def;
val _ = show "db_to_set_typed=" db_varsTheory.db_to_set_def;
val _ = show "vars_to_list_typed=" db_varsTheory.vars_to_list_def;
val _ = show "vars_from_list_typed=" db_varsTheory.vars_from_list_def;
val _ = show "vars_flatten_typed=" db_varsTheory.vars_flatten_def;
val _ = show "has_var_typed=" db_varsTheory.has_var_def;
