(* Typed captures of the REPL reference-type helpers. *)
load "preamble";
load "repl_typesTheory";
open HolKernel Parse boolLib bossLib;
open preamble repl_typesTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun show_cons label cs = (print (label ^ "=");
  print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs)); print "\n");

val _ = show_cons "simple_type_typed" [``repl_types$Bool``, ``repl_types$Str``, ``repl_types$Exn``];
val _ = show "to_type_def_typed" repl_typesTheory.to_type_def;
val _ = show "to_type_TS_def_typed" repl_typesTheory.to_type_TS_def;
val _ = show "roll_back_def_typed" repl_typesTheory.roll_back_def;
val _ = show "FST_roll_back_typed" repl_typesTheory.FST_roll_back;
val _ = show "SND_roll_back_typed" repl_typesTheory.SND_roll_back;
val _ = show "convert_t_to_type_typed" repl_typesTheory.convert_t_to_type;

(* Task 273: the set_ids range facts. *)
val _ = show "DISJOINT_set_ids_typed" repl_typesTheory.DISJOINT_set_ids;
val _ = show "set_ids_SUBSET_typed" repl_typesTheory.set_ids_SUBSET;
val _ = show "set_ids_UNION_typed" repl_typesTheory.set_ids_UNION;

(* Task 273: the REPL reference-type predicates. *)
val _ = show "check_ref_types_def_typed" repl_typesTheory.check_ref_types_def;
val _ = show "check_ref_types_TS_def_typed" repl_typesTheory.check_ref_types_TS_def;
