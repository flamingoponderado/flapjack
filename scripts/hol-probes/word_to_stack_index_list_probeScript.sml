load "bossLib"; load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
fun print_eval label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = print_eval "il_empty" ``index_list ([]:num list) 5 = []``;
val _ = print_eval "il_single" ``index_list [9n] 5 = [(5n,9n)]``;
val _ = print_eval "il_desc" ``index_list [7n;8n;9n] 4 = [(6n,7n);(5n,8n);(4n,9n)]``;
val _ = print_eval "an_even" ``adjust_names 8 = 4``;
val _ = print_eval "an_odd" ``adjust_names 9 = 4``;
