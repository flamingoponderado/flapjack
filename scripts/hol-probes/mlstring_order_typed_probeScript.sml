(* Typed captures for the mlstring ordering definitions (task 273): the indexed
   `compare_aux`/`compare` pair, the four ordering predicates and their length
   shortcuts, and the `collate_aux`/`collate` pair used by the lexer. *)
load "preamble";
load "mlstringTheory";
open HolKernel Parse boolLib bossLib;
open preamble mlstringTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "mlstring", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in mlstring>\n");

val _ = emit "compare_aux_def_typed" "compare_aux_def";
val _ = emit "compare_def_typed" "compare_def";
val _ = emit "mlstring_lt_def_typed" "mlstring_lt_def";
val _ = emit "mlstring_le_def_typed" "mlstring_le_def";
val _ = emit "mlstring_gt_def_typed" "mlstring_gt_def";
val _ = emit "mlstring_ge_def_typed" "mlstring_ge_def";
val _ = emit "fast_lt_def_typed" "fast_lt_def";
val _ = emit "fast_le_def_typed" "fast_le_def";
val _ = emit "fast_gt_def_typed" "fast_gt_def";
val _ = emit "fast_ge_def_typed" "fast_ge_def";
val _ = emit "collate_aux_def_typed" "collate_aux_def";
val _ = emit "collate_def_typed" "collate_def";
val _ = emit "compare_thm_typed" "compare_thm";
