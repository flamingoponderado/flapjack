load "preamble"; load "asmSemTheory"; load "asmPropsTheory";
open HolKernel Parse bossLib preamble asmSemTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
fun out label tm = let val th = EVAL tm val r = rhs(concl th) in
 if null(hyp th) andalso aconv r ``T`` then
 (print(label ^ "="); print_term r; print "\n")
 else raise Fail ("non-true original source memory observation: " ^ label) end;
val _ = out "le0_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 0 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (255w:8 word) 0 (0x1234w:16 word) s).failed = F``;
val _ = out "le1_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 1 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (255w:8 word) 1 (0x1234w:16 word) s).failed = F``;
val _ = out "le1_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 1 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (255w:8 word) 1 (0x1234w:16 word) s).failed = T``;
val _ = out "le2_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word);(0w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 2 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (255w:8 word) 2 (0x1234w:16 word) s).failed = F``;
val _ = out "le2_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 2 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (255w:8 word) 2 (0x1234w:16 word) s).failed = T``;
val _ = out "le4_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word);(0w:8 word);(1w:8 word);(2w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 4 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (255w:8 word) 4 (0x1234w:16 word) s).failed = F``;
val _ = out "le4_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word);(0w:8 word);(1w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 4 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (255w:8 word) 4 (0x1234w:16 word) s).failed = T``;
val _ = out "le8_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word);(0w:8 word);(1w:8 word);(2w:8 word);(3w:8 word);(4w:8 word);(5w:8 word);(6w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 8 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (255w:8 word) 8 (0x1234w:16 word) s).failed = F``;
val _ = out "le8_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word);(0w:8 word);(1w:8 word);(2w:8 word);(3w:8 word);(4w:8 word);(5w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 8 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (255w:8 word) 8 (0x1234w:16 word) s).failed = T``;
val _ = out "le12_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word);(0w:8 word);(1w:8 word);(2w:8 word);(3w:8 word);(4w:8 word);(5w:8 word);(6w:8 word);(7w:8 word);(8w:8 word);(9w:8 word);(10w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 12 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (255w:8 word) 12 (0x1234w:16 word) s).failed = F``;
val _ = out "le12_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(255w:8 word);(0w:8 word);(1w:8 word);(2w:8 word);(3w:8 word);(4w:8 word);(5w:8 word);(6w:8 word);(7w:8 word);(8w:8 word);(9w:8 word)}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (255w:8 word) 12 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (255w:8 word) 12 (0x1234w:16 word) s).failed = T``;
val _ = out "be0_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 0 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (1w:8 word) 0 (0x1234w:16 word) s).failed = F``;
val _ = out "be1_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 1 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (1w:8 word) 1 (0x1234w:16 word) s).failed = F``;
val _ = out "be1_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 1 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (1w:8 word) 1 (0x1234w:16 word) s).failed = T``;
val _ = out "be2_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word);(0w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 2 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (1w:8 word) 2 (0x1234w:16 word) s).failed = F``;
val _ = out "be2_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 2 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (1w:8 word) 2 (0x1234w:16 word) s).failed = T``;
val _ = out "be4_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word);(0w:8 word);(255w:8 word);(254w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 4 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (1w:8 word) 4 (0x1234w:16 word) s).failed = F``;
val _ = out "be4_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word);(0w:8 word);(255w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 4 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (1w:8 word) 4 (0x1234w:16 word) s).failed = T``;
val _ = out "be8_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word);(0w:8 word);(255w:8 word);(254w:8 word);(253w:8 word);(252w:8 word);(251w:8 word);(250w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 8 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (1w:8 word) 8 (0x1234w:16 word) s).failed = F``;
val _ = out "be8_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word);(0w:8 word);(255w:8 word);(254w:8 word);(253w:8 word);(252w:8 word);(251w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 8 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (1w:8 word) 8 (0x1234w:16 word) s).failed = T``;
val _ = out "be12_wrap" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word);(0w:8 word);(255w:8 word);(254w:8 word);(253w:8 word);(252w:8 word);(251w:8 word);(250w:8 word);(249w:8 word);(248w:8 word);(247w:8 word);(246w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 12 s : 16 word # 8 asm_state)).failed = F /\
 (write_mem_word (1w:8 word) 12 (0x1234w:16 word) s).failed = F``;
val _ = out "be12_missing" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. a); mem_domain := {(1w:8 word);(0w:8 word);(255w:8 word);(254w:8 word);(253w:8 word);(252w:8 word);(251w:8 word);(250w:8 word);(249w:8 word);(248w:8 word);(247w:8 word)}; pc := 0w; lr := 0; align := 0; be := T; failed := F |> : 8 asm_state) in
 (SND (read_mem_word (1w:8 word) 12 s : 16 word # 8 asm_state)).failed = T /\
 (write_mem_word (1w:8 word) 12 (0x1234w:16 word) s).failed = T``;
val _ = out "previous_failure_zero" ``let s = ((ARB:8 asm_state) with failed := T) in
 (SND (read_mem_word (0w:8 word) 0 s : 16 word # 8 asm_state)).failed /\
 (write_mem_word (0w:8 word) 0 (0w:16 word) s).failed``;
val tm = ``read_mem_word (a:8 word) (SUC n) (s:8 asm_state) : 16 word # 8 asm_state``;
val th = SIMP_CONV (srw_ss()) [read_mem_word_def] tm;
val _ = (print "read_clause="; print_term(concl th); print "\n");
val _ = print ("read_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print ("read_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm)) ^ "\n");
val tm = ``write_mem_word (a:8 word) (SUC n) (v:16 word) (s:8 asm_state)``;
val th = SIMP_CONV (srw_ss()) [write_mem_word_def] tm;
val _ = (print "write_clause="; print_term(concl th); print "\n");
val _ = print ("write_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print ("write_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm)) ^ "\n");
val tm = ``mem_load n r (Addr rb (off:8 word)) (s:8 asm_state)``;
val th = SIMP_CONV (srw_ss()) [mem_load_def] tm;
val _ = (print "load_clause="; print_term(concl th); print "\n");
val _ = print ("load_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print ("load_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm)) ^ "\n");
val tm = ``mem_store n r (Addr rb (off:8 word)) (s:8 asm_state)``;
val th = SIMP_CONV (srw_ss()) [mem_store_def] tm;
val _ = (print "store_clause="; print_term(concl th); print "\n");
val _ = print ("store_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print ("store_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
