(* Original HOL types of linear_scan/reg_alloc constants whose carriers are
   polymorphic (unused or uninspected arguments, generic exceptions), checked
   against the Lean binders. CakeML remains read-only. *)
load "bossLib";
load "linear_scanTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000;
fun ty label thy name =
  (print (label ^ "=");
   print_type (type_of (prim_mk_const {Thy = thy, Name = name}));
   print "\n");
val _ = ty "check_col" "reg_alloc" "check_col";
val _ = ty "check_intervals" "linear_scan" "check_intervals";
val _ = ty "colors_length" "linear_scan" "colors_length";
val _ = ty "int_beg_length" "linear_scan" "int_beg_length";
val _ = ty "int_end_length" "linear_scan" "int_end_length";
val _ = ty "sorted_regs_length" "linear_scan" "sorted_regs_length";
val _ = ty "sorted_moves_length" "linear_scan" "sorted_moves_length";
val _ = ty "find_last_stealable" "linear_scan" "find_last_stealable";
val _ = ty "run_i_linear_scan_hidden_state" "linear_scan" "run_i_linear_scan_hidden_state";
val _ = ty "linear_reg_alloc_and_extract_coloration" "linear_scan" "linear_reg_alloc_and_extract_coloration";
val _ = ty "i_linear_scan_hidden_state_CASE" "linear_scan" "i_linear_scan_hidden_state_CASE";
