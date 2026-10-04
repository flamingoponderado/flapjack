load "preamble"; load "riscv_targetTheory"; load "asmSemTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_targetTheory asmTheory asmSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = computeLib.add_funs [rawWriteData_def,MEM_def,write'MEM_def];
fun out label tm = let
 val th = (EVAL THENC SIMP_CONV (srw_ss()) [riscv_state_fn_updates] THENC EVAL) tm
 val r = rhs(concl th) in
 if null(hyp th) andalso aconv r ``T`` then
 (print(label ^ "="); print_term r; print "\n")
 else (print_term r; print "\n"; raise Fail ("non-true original store post-memory observation: " ^ label)) end;
val _ = out "store1_zero" ``let bytes = (\p. w2w (p + 128w):word8) in
 let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (0w:word64) 1 (9833440827789222417w:word64) initial in
 let native = rawWriteData ((0w:word64),(9833440827789222417w:word64),1) ((ARB:riscv_state) with MEM8 := bytes) in
 source.mem 0w = 17w /\ native.MEM8 0w = 17w /\ source.mem 18446744073709551615w = 127w /\ native.MEM8 18446744073709551615w = 127w /\ source.mem 1w = 129w /\ native.MEM8 1w = 129w /\ source.mem 42w = 170w /\ native.MEM8 42w = 170w /\ source.failed = F /\ source.mem_domain = initial.mem_domain /\ source.regs = initial.regs /\ source.fp_regs = initial.fp_regs /\ source.pc = initial.pc /\ source.lr = initial.lr /\ source.be = initial.be /\ source.align = initial.align``;
val _ = out "store1_wrap" ``let bytes = (\p. w2w (p + 128w):word8) in
 let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (18446744073709551615w:word64) 1 (9833440827789222417w:word64) initial in
 let native = rawWriteData ((18446744073709551615w:word64),(9833440827789222417w:word64),1) ((ARB:riscv_state) with MEM8 := bytes) in
 source.mem 18446744073709551615w = 17w /\ native.MEM8 18446744073709551615w = 17w /\ source.mem 18446744073709551614w = 126w /\ native.MEM8 18446744073709551614w = 126w /\ source.mem 0w = 128w /\ native.MEM8 0w = 128w /\ source.mem 42w = 170w /\ native.MEM8 42w = 170w /\ source.failed = F /\ source.mem_domain = initial.mem_domain /\ source.regs = initial.regs /\ source.fp_regs = initial.fp_regs /\ source.pc = initial.pc /\ source.lr = initial.lr /\ source.be = initial.be /\ source.align = initial.align``;
val _ = out "store2_zero" ``let bytes = (\p. w2w (p + 128w):word8) in
 let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (0w:word64) 2 (9833440827789222417w:word64) initial in
 let native = rawWriteData ((0w:word64),(9833440827789222417w:word64),2) ((ARB:riscv_state) with MEM8 := bytes) in
 source.mem 0w = 17w /\ native.MEM8 0w = 17w /\ source.mem 1w = 34w /\ native.MEM8 1w = 34w /\ source.mem 18446744073709551615w = 127w /\ native.MEM8 18446744073709551615w = 127w /\ source.mem 2w = 130w /\ native.MEM8 2w = 130w /\ source.mem 42w = 170w /\ native.MEM8 42w = 170w /\ source.failed = F /\ source.mem_domain = initial.mem_domain /\ source.regs = initial.regs /\ source.fp_regs = initial.fp_regs /\ source.pc = initial.pc /\ source.lr = initial.lr /\ source.be = initial.be /\ source.align = initial.align``;
val _ = out "store2_wrap" ``let bytes = (\p. w2w (p + 128w):word8) in
 let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (18446744073709551614w:word64) 2 (9833440827789222417w:word64) initial in
 let native = rawWriteData ((18446744073709551614w:word64),(9833440827789222417w:word64),2) ((ARB:riscv_state) with MEM8 := bytes) in
 source.mem 18446744073709551614w = 17w /\ native.MEM8 18446744073709551614w = 17w /\ source.mem 18446744073709551615w = 34w /\ native.MEM8 18446744073709551615w = 34w /\ source.mem 18446744073709551613w = 125w /\ native.MEM8 18446744073709551613w = 125w /\ source.mem 0w = 128w /\ native.MEM8 0w = 128w /\ source.mem 42w = 170w /\ native.MEM8 42w = 170w /\ source.failed = F /\ source.mem_domain = initial.mem_domain /\ source.regs = initial.regs /\ source.fp_regs = initial.fp_regs /\ source.pc = initial.pc /\ source.lr = initial.lr /\ source.be = initial.be /\ source.align = initial.align``;
val _ = out "store4_zero" ``let bytes = (\p. w2w (p + 128w):word8) in
 let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (0w:word64) 4 (9833440827789222417w:word64) initial in
 let native = rawWriteData ((0w:word64),(9833440827789222417w:word64),4) ((ARB:riscv_state) with MEM8 := bytes) in
 source.mem 0w = 17w /\ native.MEM8 0w = 17w /\ source.mem 1w = 34w /\ native.MEM8 1w = 34w /\ source.mem 2w = 51w /\ native.MEM8 2w = 51w /\ source.mem 3w = 68w /\ native.MEM8 3w = 68w /\ source.mem 18446744073709551615w = 127w /\ native.MEM8 18446744073709551615w = 127w /\ source.mem 4w = 132w /\ native.MEM8 4w = 132w /\ source.mem 42w = 170w /\ native.MEM8 42w = 170w /\ source.failed = F /\ source.mem_domain = initial.mem_domain /\ source.regs = initial.regs /\ source.fp_regs = initial.fp_regs /\ source.pc = initial.pc /\ source.lr = initial.lr /\ source.be = initial.be /\ source.align = initial.align``;
val _ = out "store4_wrap" ``let bytes = (\p. w2w (p + 128w):word8) in
 let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (18446744073709551612w:word64) 4 (9833440827789222417w:word64) initial in
 let native = rawWriteData ((18446744073709551612w:word64),(9833440827789222417w:word64),4) ((ARB:riscv_state) with MEM8 := bytes) in
 source.mem 18446744073709551612w = 17w /\ native.MEM8 18446744073709551612w = 17w /\ source.mem 18446744073709551613w = 34w /\ native.MEM8 18446744073709551613w = 34w /\ source.mem 18446744073709551614w = 51w /\ native.MEM8 18446744073709551614w = 51w /\ source.mem 18446744073709551615w = 68w /\ native.MEM8 18446744073709551615w = 68w /\ source.mem 18446744073709551611w = 123w /\ native.MEM8 18446744073709551611w = 123w /\ source.mem 0w = 128w /\ native.MEM8 0w = 128w /\ source.mem 42w = 170w /\ native.MEM8 42w = 170w /\ source.failed = F /\ source.mem_domain = initial.mem_domain /\ source.regs = initial.regs /\ source.fp_regs = initial.fp_regs /\ source.pc = initial.pc /\ source.lr = initial.lr /\ source.be = initial.be /\ source.align = initial.align``;
val _ = out "store8_zero" ``let bytes = (\p. w2w (p + 128w):word8) in
 let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (0w:word64) 8 (9833440827789222417w:word64) initial in
 let native = rawWriteData ((0w:word64),(9833440827789222417w:word64),8) ((ARB:riscv_state) with MEM8 := bytes) in
 source.mem 0w = 17w /\ native.MEM8 0w = 17w /\ source.mem 1w = 34w /\ native.MEM8 1w = 34w /\ source.mem 2w = 51w /\ native.MEM8 2w = 51w /\ source.mem 3w = 68w /\ native.MEM8 3w = 68w /\ source.mem 4w = 85w /\ native.MEM8 4w = 85w /\ source.mem 5w = 102w /\ native.MEM8 5w = 102w /\ source.mem 6w = 119w /\ native.MEM8 6w = 119w /\ source.mem 7w = 136w /\ native.MEM8 7w = 136w /\ source.mem 18446744073709551615w = 127w /\ native.MEM8 18446744073709551615w = 127w /\ source.mem 8w = 136w /\ native.MEM8 8w = 136w /\ source.mem 42w = 170w /\ native.MEM8 42w = 170w /\ source.failed = F /\ source.mem_domain = initial.mem_domain /\ source.regs = initial.regs /\ source.fp_regs = initial.fp_regs /\ source.pc = initial.pc /\ source.lr = initial.lr /\ source.be = initial.be /\ source.align = initial.align``;
val _ = out "store8_wrap" ``let bytes = (\p. w2w (p + 128w):word8) in
 let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := bytes; mem_domain := UNIV; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (18446744073709551608w:word64) 8 (9833440827789222417w:word64) initial in
 let native = rawWriteData ((18446744073709551608w:word64),(9833440827789222417w:word64),8) ((ARB:riscv_state) with MEM8 := bytes) in
 source.mem 18446744073709551608w = 17w /\ native.MEM8 18446744073709551608w = 17w /\ source.mem 18446744073709551609w = 34w /\ native.MEM8 18446744073709551609w = 34w /\ source.mem 18446744073709551610w = 51w /\ native.MEM8 18446744073709551610w = 51w /\ source.mem 18446744073709551611w = 68w /\ native.MEM8 18446744073709551611w = 68w /\ source.mem 18446744073709551612w = 85w /\ native.MEM8 18446744073709551612w = 85w /\ source.mem 18446744073709551613w = 102w /\ native.MEM8 18446744073709551613w = 102w /\ source.mem 18446744073709551614w = 119w /\ native.MEM8 18446744073709551614w = 119w /\ source.mem 18446744073709551615w = 136w /\ native.MEM8 18446744073709551615w = 136w /\ source.mem 18446744073709551607w = 119w /\ native.MEM8 18446744073709551607w = 119w /\ source.mem 0w = 128w /\ native.MEM8 0w = 128w /\ source.mem 42w = 170w /\ native.MEM8 42w = 170w /\ source.failed = F /\ source.mem_domain = initial.mem_domain /\ source.regs = initial.regs /\ source.fp_regs = initial.fp_regs /\ source.pc = initial.pc /\ source.lr = initial.lr /\ source.be = initial.be /\ source.align = initial.align``;
val _ = out "source_failure_writes" ``let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\p. 99w); mem_domain := {}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (0w:word64) 2 (1w:64 word) initial in
 source.failed = T /\ source.mem 0w = 1w /\ source.mem 1w = 0w /\ source.mem 2w = 99w``;
val _ = out "source_narrow_value" ``let initial = (<| regs := (\r. 0w); fp_regs := (\r. 0w); mem := (\p. 99w); mem_domain := {}; pc := 0w; lr := 0; align := 0; be := F; failed := F |> : 64 asm_state) in
 let source = write_mem_word (0w:word64) 2 (1w:1 word) initial in
 source.failed = T /\ source.mem 0w = 1w /\ source.mem 1w = 0w /\ source.mem 2w = 99w``;
val tm = ``write_mem_word (p:word64) (SUC n) (v:word64) (s:64 asm_state)``;
val th = SIMP_CONV (srw_ss()) [write_mem_word_def] tm;
val _ = (print "source_clause="; print_term(concl th); print "\n");
val _ = print ("source_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print ("source_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm)) ^ "\n");
val tm = ``rawWriteData ((p:word64),(v:word64),n) t``;
val th = SIMP_CONV (srw_ss()) [rawWriteData_def] tm;
val _ = (print "native_clause="; print_term(concl th); print "\n");
val _ = print ("native_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print ("native_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
