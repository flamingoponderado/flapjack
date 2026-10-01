(* Direct original labSem loc_to_pc observations on section-valid fixtures.
   These exercise the boundary decomposed by loc_to_pc_thm, not a substitute evaluator. *)
load "bossLib";
load "preamble";
load "labSemTheory";
open bossLib HolKernel Parse preamble labSemTheory;
fun print_eval label q = let val th = (SIMP_CONV (srw_ss()) [loc_to_pc_def] THENC EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL) q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val lines = ``[Asm (Cbw 1 2) [] 99; Label 1 5 42; LabAsm Halt 0w [] 88; Label 1 7 43] : 8 labLang$line list``;
val one = ``[Section 1 ^lines] : 8 labLang$prog``;
val code = ``[Section 9 [Asm (Cbw 3 4) [] 100; Label 9 8 44]; Section 1 ^lines; Section 2 []] : 8 labLang$prog``;
val _ = print_eval "section_entry" ``loc_to_pc 1 0 ^one = SOME 0``;
val _ = print_eval "section_label5" ``loc_to_pc 1 5 ^one = SOME 1``;
val _ = print_eval "section_label7" ``loc_to_pc 1 7 ^one = SOME 2``;
val _ = print_eval "section_missing" ``loc_to_pc 1 99 ^one = NONE``;
val _ = print_eval "preceding_entry" ``loc_to_pc 1 0 ^code = SOME 1``;
val _ = print_eval "preceding_label5" ``loc_to_pc 1 5 ^code = SOME 2``;
val _ = print_eval "empty_tail_entry" ``loc_to_pc 2 0 ^code = SOME 3``;
val _ = print_eval "empty_tail_missing" ``loc_to_pc 2 5 ^code = NONE``;
