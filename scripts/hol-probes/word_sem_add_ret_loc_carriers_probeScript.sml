load "bossLib";
load "wordSemTheory";
open HolKernel Parse bossLib wordSemTheory;
val _ = Globals.linewidth := 1000000;
fun typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
fun hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun eval label q = (print (label ^ "="); print_term (boolSyntax.rhs (concl (EVAL q))); print "\n");
val _ = typed "add_ret_loc_independent_metadata_typed" add_ret_loc_def;
val _ = hyps "add_ret_loc_independent_metadata_hypotheses" add_ret_loc_def;
val _ = eval "add_ret_loc_independent_metadata_some"
  ``add_ret_loc (SOME (T,(9:num,10:num),(17w:word32),5:num,6:num)) [Word 7w : 8 word_loc]``;
val _ = eval "add_ret_loc_independent_metadata_none"
  ``add_ret_loc (NONE : (bool # (num # num) # word32 # num # num) option) [Word 7w : 8 word_loc]``;
