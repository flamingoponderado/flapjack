(* Typed captures for the remaining semanticPrimitives type-number constants
   (task 273): the constructor type stamps used by the source value encoding. *)
load "preamble";
load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
open preamble semanticPrimitivesTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "semanticPrimitives", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in semanticPrimitives>\n");

val _ = emit "lit_type_num_def_typed" "lit_type_num_def";
val _ = emit "ast_t_type_num_def_typed" "ast_t_type_num_def";
val _ = emit "pat_type_num_def_typed" "pat_type_num_def";
val _ = emit "lop_type_num_def_typed" "lop_type_num_def";
val _ = emit "opn_type_num_def_typed" "opn_type_num_def";
val _ = emit "opb_type_num_def_typed" "opb_type_num_def";
val _ = emit "opw_type_num_def_typed" "opw_type_num_def";
val _ = emit "shift_type_num_def_typed" "shift_type_num_def";
val _ = emit "word_size_type_num_def_typed" "word_size_type_num_def";
val _ = emit "fp_uop_type_num_def_typed" "fp_uop_type_num_def";
val _ = emit "fp_bop_type_num_def_typed" "fp_bop_type_num_def";
val _ = emit "fp_top_type_num_def_typed" "fp_top_type_num_def";
val _ = emit "fp_cmp_type_num_def_typed" "fp_cmp_type_num_def";
val _ = emit "op_type_num_def_typed" "op_type_num_def";
val _ = emit "locn_type_num_def_typed" "locn_type_num_def";
val _ = emit "locs_type_num_def_typed" "locs_type_num_def";
val _ = emit "exp_type_num_def_typed" "exp_type_num_def";
val _ = emit "dec_type_num_def_typed" "dec_type_num_def";
