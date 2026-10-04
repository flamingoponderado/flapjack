load "preamble"; load "asmSemTheory";
open HolKernel Parse bossLib preamble asmSemTheory;
val _ = Globals.linewidth := 1000000;
fun out label tm = let val th = EVAL tm val r = rhs(concl th) in
 if null(hyp th) andalso aconv r ``T`` then
 (print(label ^ "="); print_term r; print "\n")
 else raise Fail ("non-true original byte shift observation: " ^ label) end;
val _ = out "read_width_1" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. if a = 1w then 1w else 0w); mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in (FST (read_mem_word (0w:8 word) 2 s) : 1 word) = 0w``;
val _ = out "write_width_1" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. if a = 1w then 1w else 0w); mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in (write_mem_word (0w:8 word) 2 (1w:1 word) s).mem 0w = 1w /\ (write_mem_word (0w:8 word) 2 (1w:1 word) s).mem 1w = 0w /\ (write_mem_word (0w:8 word) 2 (1w:1 word) s).failed = F``;
val _ = out "read_width_2" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. if a = 1w then 1w else 0w); mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in (FST (read_mem_word (0w:8 word) 2 s) : 2 word) = 0w``;
val _ = out "write_width_2" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. if a = 1w then 1w else 0w); mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in (write_mem_word (0w:8 word) 2 (1w:2 word) s).mem 0w = 1w /\ (write_mem_word (0w:8 word) 2 (1w:2 word) s).mem 1w = 0w /\ (write_mem_word (0w:8 word) 2 (1w:2 word) s).failed = F``;
val _ = out "read_width_3" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. if a = 1w then 1w else 0w); mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in (FST (read_mem_word (0w:8 word) 2 s) : 3 word) = 0w``;
val _ = out "write_width_3" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. if a = 1w then 1w else 0w); mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in (write_mem_word (0w:8 word) 2 (1w:3 word) s).mem 0w = 1w /\ (write_mem_word (0w:8 word) 2 (1w:3 word) s).mem 1w = 0w /\ (write_mem_word (0w:8 word) 2 (1w:3 word) s).failed = F``;
val _ = out "read_width_64" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. if a = 1w then 1w else 0w); mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in (FST (read_mem_word (0w:8 word) 2 s) : 64 word) = 256w``;
val _ = out "write_width_64" ``let s = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\a. if a = 1w then 1w else 0w); mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 8 asm_state) in (write_mem_word (0w:8 word) 2 (1w:64 word) s).mem 0w = 1w /\ (write_mem_word (0w:8 word) 2 (1w:64 word) s).mem 1w = 0w /\ (write_mem_word (0w:8 word) 2 (1w:64 word) s).failed = F``;
val _ = OS.Process.exit OS.Process.success;
