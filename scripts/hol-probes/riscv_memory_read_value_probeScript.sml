load "preamble"; load "riscv_targetTheory"; load "asmSemTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_targetTheory asmTheory asmSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = computeLib.add_funs [rawReadData_def,MEM_def];
fun out label tm = let
 val th = (EVAL THENC SIMP_CONV (srw_ss()) [riscv_state_fn_updates] THENC EVAL) tm
 val r = rhs(concl th) in
 if null(hyp th) andalso aconv r ``T`` then
 (print(label ^ "="); print_term r; print "\n")
 else (print_term r; print "\n"; raise Fail ("non-true original source/native read value: " ^ label)) end;
val _ = out "read1_zero" ``let a = (0w:word64) in
 let bytes = (\p. w2w (p + 128w):word8) in
 let source = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let native = (ARB:riscv_state) with MEM8 := bytes in
 (FST (read_mem_word a 1 source):word64) = 128w /\
 (word_extract 7 0 (rawReadData a native):word64) = 128w``;
val _ = out "read1_wrap" ``let a = (18446744073709551615w:word64) in
 let bytes = (\p. w2w (p + 128w):word8) in
 let source = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let native = (ARB:riscv_state) with MEM8 := bytes in
 (FST (read_mem_word a 1 source):word64) = 127w /\
 (word_extract 7 0 (rawReadData a native):word64) = 127w``;
val _ = out "read2_zero" ``let a = (0w:word64) in
 let bytes = (\p. w2w (p + 128w):word8) in
 let source = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let native = (ARB:riscv_state) with MEM8 := bytes in
 (FST (read_mem_word a 2 source):word64) = 33152w /\
 (word_extract 15 0 (rawReadData a native):word64) = 33152w``;
val _ = out "read2_wrap" ``let a = (18446744073709551614w:word64) in
 let bytes = (\p. w2w (p + 128w):word8) in
 let source = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let native = (ARB:riscv_state) with MEM8 := bytes in
 (FST (read_mem_word a 2 source):word64) = 32638w /\
 (word_extract 15 0 (rawReadData a native):word64) = 32638w``;
val _ = out "read4_zero" ``let a = (0w:word64) in
 let bytes = (\p. w2w (p + 128w):word8) in
 let source = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let native = (ARB:riscv_state) with MEM8 := bytes in
 (FST (read_mem_word a 4 source):word64) = 2206368128w /\
 (word_extract 31 0 (rawReadData a native):word64) = 2206368128w``;
val _ = out "read4_wrap" ``let a = (18446744073709551612w:word64) in
 let bytes = (\p. w2w (p + 128w):word8) in
 let source = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let native = (ARB:riscv_state) with MEM8 := bytes in
 (FST (read_mem_word a 4 source):word64) = 2138996092w /\
 (word_extract 31 0 (rawReadData a native):word64) = 2138996092w``;
val _ = out "read8_zero" ``let a = (0w:word64) in
 let bytes = (\p. w2w (p + 128w):word8) in
 let source = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let native = (ARB:riscv_state) with MEM8 := bytes in
 (FST (read_mem_word a 8 source):word64) = 9765639646188044672w /\
 (word_extract 63 0 (rawReadData a native):word64) = 9765639646188044672w``;
val _ = out "read8_wrap" ``let a = (18446744073709551608w:word64) in
 let bytes = (\p. w2w (p + 128w):word8) in
 let source = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let native = (ARB:riscv_state) with MEM8 := bytes in
 (FST (read_mem_word a 8 source):word64) = 9186918263483431288w /\
 (word_extract 63 0 (rawReadData a native):word64) = 9186918263483431288w``;
val tm = ``read_mem_word (p:word64) (SUC n) (s:64 asm_state) : word64 # 64 asm_state``;
val th = SIMP_CONV (srw_ss()) [read_mem_word_def] tm;
val _ = (print "source_clause="; print_term(concl th); print "\n");
val _ = print ("source_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print ("source_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm)) ^ "\n");
val tm = ``rawReadData (p:word64) t``;
val th = SIMP_CONV (srw_ss()) [rawReadData_def] tm;
val _ = (print "native_clause="; print_term(concl th); print "\n");
val _ = print ("native_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print ("native_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
