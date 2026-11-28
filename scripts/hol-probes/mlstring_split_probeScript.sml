(* Typed captures of the mlstring splitting definitions and their filter fact. *)
load "mlstringTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "splitl_aux_def_typed" mlstringTheory.splitl_aux_def;
val _ = show "splitl_def_typed" mlstringTheory.splitl_def;
val _ = show "tokens_aux_def_typed" mlstringTheory.tokens_aux_def;
val _ = show "tokens_def_typed" mlstringTheory.tokens_def;
val _ = show "tokens_filter_typed" mlstringTheory.tokens_filter;
