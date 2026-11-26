(* Typed captures of the misc find_index/anub facts and HOL INDEX_OF. *)
load "preamble";
load "miscTheory";
open HolKernel Parse boolLib bossLib;
open preamble miscTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "INDEX_OF_def_typed" listTheory.INDEX_OF_def;
val _ = show "find_index_ALL_DISTINCT_EL_typed" miscTheory.find_index_ALL_DISTINCT_EL;
val _ = show "find_index_INDEX_OF_typed" miscTheory.find_index_INDEX_OF;
val _ = show "EVERY_anub_imp_typed" miscTheory.EVERY_anub_imp;
