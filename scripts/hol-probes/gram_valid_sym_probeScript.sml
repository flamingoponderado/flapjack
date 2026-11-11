(* Typed source declarations for the grammar operator predicates in
   cakeml/semantics/gramScript.sml. *)
load "gramTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "valid_mult_sym_def_typed" gramTheory.validMultSym_def;
val _ = show "valid_add_sym_def_typed" gramTheory.validAddSym_def;
val _ = show "valid_rel_sym_def_typed" gramTheory.validRelSym_def;
val _ = show "valid_list_sym_def_typed" gramTheory.validListSym_def;
val _ = show "valid_prefix_sym_def_typed" gramTheory.validPrefixSym_def;
