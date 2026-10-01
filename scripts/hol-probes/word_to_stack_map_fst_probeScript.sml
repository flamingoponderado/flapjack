load "bossLib"; load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
fun print_eval label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = print_eval "mf_empty" ``MAP_FST (\n:num. n DIV 2) ([]:(num#num) list) = []``;
val _ = print_eval "mf_keys" ``MAP_FST (\n:num. n DIV 2) [(6n,7n);(4n,8n);(2n,9n)] = [(3n,7n);(2n,8n);(1n,9n)]``;
val _ = print_eval "mf_collision" ``MAP_FST (\n:num. 0n) [(6n,7n);(4n,8n)] = [(0n,7n);(0n,8n)]``;
val _ = print_eval "mf_values" ``MAP SND (MAP_FST (\n:num. n DIV 2) [(6n,7n);(4n,8n);(2n,9n)]) = [7n;8n;9n]``;
