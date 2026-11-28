(* Typed captures for the mlstring ordering definitions (task 273): the indexed
   `compare_aux`/`compare` pair, the four ordering predicates and their length
   shortcuts, the `collate_aux`/`collate` pair used by the lexer, and the order
   theorems with their `stringTheory`/`relationTheory` prerequisites. *)
load "preamble";
load "relationTheory";
load "mlstringTheory";
open HolKernel Parse boolLib bossLib;
open preamble relationTheory mlstringTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "mlstring", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in mlstring>\n");

fun emitIn label thy name =
  case DB.lookup {Thy = thy, Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in " ^ thy ^ ">\n");

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

(* Ordering theorems and the string/relation prerequisites. *)
val _ = emitIn "string_lt_def_typed" "string" "string_lt_def";
val _ = emitIn "string_le_def_typed" "string" "string_le_def";
val _ = emit "string_lt_total_typed" "string_lt_total";
val _ = emitIn "string_lt_nonrefl_typed" "string" "string_lt_nonrefl";
val _ = emitIn "string_lt_antisym_typed" "string" "string_lt_antisym";
val _ = emitIn "string_lt_cases_typed" "string" "string_lt_cases";
val _ = emitIn "string_lt_trans_typed" "string" "string_lt_trans";
val _ = emitIn "antisymmetric_def_typed" "relation" "antisymmetric_def";
val _ = emitIn "trichotomous_typed" "relation" "trichotomous";
val _ = emitIn "StrongOrder_typed" "relation" "StrongOrder";
val _ = emitIn "StrongLinearOrder_typed" "relation" "StrongLinearOrder";
val _ = emit "mlstring_lt_inv_image_typed" "mlstring_lt_inv_image";
val _ = emit "TotOrd_compare_typed" "TotOrd_compare";
val _ = emit "good_cmp_compare_typed" "good_cmp_compare";
val _ = emit "mlstring_lt_antisym_typed" "mlstring_lt_antisym";
val _ = emit "mlstring_lt_cases_typed" "mlstring_lt_cases";
val _ = emit "mlstring_lt_nonrefl_typed" "mlstring_lt_nonrefl";
val _ = emit "mlstring_lt_trans_typed" "mlstring_lt_trans";
val _ = emit "mlstring_le_thm_typed" "mlstring_le_thm";
val _ = emit "mlstring_gt_thm_typed" "mlstring_gt_thm";
val _ = emit "mlstring_ge_thm_typed" "mlstring_ge_thm";
val _ = emit "transitive_mlstring_le_typed" "transitive_mlstring_le";
val _ = emit "antisymmetric_mlstring_le_typed" "antisymmetric_mlstring_le";
val _ = emit "total_mlstring_le_typed" "total_mlstring_le";
val _ = emit "strlit_le_strlit_typed" "strlit_le_strlit";
val _ = emit "StrongLinearOrder_mlstring_lt_typed" "StrongLinearOrder_mlstring_lt";
val _ = emit "fast_lt_nonrefl_typed" "fast_lt_nonrefl";
val _ = emit "fast_lt_trans_typed" "fast_lt_trans";
val _ = emit "fast_le_thm_typed" "fast_le_thm";
val _ = emit "fast_gt_thm_typed" "fast_gt_thm";
val _ = emit "fast_ge_thm_typed" "fast_ge_thm";
val _ = emit "transitive_fast_le_typed" "transitive_fast_le";
val _ = emit "antisymmetric_fast_le_typed" "antisymmetric_fast_le";
val _ = emit "total_fast_le_typed" "total_fast_le";
val _ = emit "transitive_fast_lt_typed" "transitive_fast_lt";
val _ = emit "irreflexive_fast_lt_typed" "irreflexive_fast_lt";
val _ = emit "trichotomous_fast_lt_typed" "trichotomous_fast_lt";
val _ = emit "StrongLinearOrder_fast_lt_typed" "StrongLinearOrder_fast_lt";
