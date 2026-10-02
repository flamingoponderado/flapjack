load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory labSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "sec_loc_to_pc_bound" sec_loc_to_pc_bound;
val _ = captureTypes "sec_loc_to_pc_bound_types" sec_loc_to_pc_bound;
val _ = capture "loc_to_pc_bound" loc_to_pc_bound;
val _ = captureTypes "loc_to_pc_bound_types" loc_to_pc_bound;
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc((SIMP_CONV (srw_ss()) [sec_loc_to_pc_def,loc_to_pc_def] THENC EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL) q)); print "\n");
val lines = ``[Asm (Cbw 1 2) [] 99; Label 1 5 42; LabAsm Halt 0w [] 88; Label 1 7 43] : 8 labLang$line list``;
val code = ``[Section 9 [Asm (Cbw 3 4) [] 100; Label 9 8 44]; Section 1 ^lines; Section 2 []] : 8 labLang$prog``;
val _ = observe "zero_empty" ``sec_loc_to_pc 0 ([]:1 labLang$line list) = SOME 0``;
val _ = observe "local_last_bound" ``sec_loc_to_pc 7 ^lines = SOME 2``;
val _ = observe "local_last_count" ``LENGTH(FILTER (λx. ~is_Label x) ^lines) = 2``;
val _ = observe "code_empty_tail_bound" ``loc_to_pc 2 0 ^code = SOME 3``;
val _ = observe "code_total_count" ``SUM(MAP (LENGTH o FILTER (λx. ~is_Label x) o Section_lines) ^code) = 3``;
val _ = observe "wide_zero_empty" ``sec_loc_to_pc 0 ([]:80 labLang$line list) = SOME 0``;
