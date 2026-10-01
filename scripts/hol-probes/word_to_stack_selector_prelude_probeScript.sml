(* Finite original RISC-V expression-selector preludes, tar=temp=23. These
   do not establish universal selector semantics or full program routing. *)
load "bossLib"; load "preamble"; load "word_instTheory"; load "riscv_targetTheory";
open HolKernel Parse bossLib preamble word_instTheory riscv_targetTheory;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "selector_prelude_const" ``inst_select_exp riscv_config 23 23 (Const (7w:64 word))``;
val _ = out "selector_prelude_var" ``inst_select_exp riscv_config 23 23 (Var 18:64 wordLang$exp)``;
val _ = out "selector_prelude_lookup" ``inst_select_exp riscv_config 23 23 (Lookup CurrHeap:64 wordLang$exp)``;
val _ = out "selector_prelude_load" ``inst_select_exp riscv_config 23 23 (Load (Var 18):64 wordLang$exp)``;
val _ = out "selector_prelude_add" ``inst_select_exp riscv_config 23 23 (Op Add [Var 18; Const (7w:64 word)])``;
val _ = out "selector_prelude_shift" ``inst_select_exp riscv_config 23 23 (Shift Lsl (Var 18) (Const 3w):64 wordLang$exp)``;
val _ = out "selector_prelude_shift_oob" ``inst_select_exp riscv_config 23 23 (Shift Lsl (Var 18) (Const 64w):64 wordLang$exp)``;
val _ = out "selector_prelude_heap" ``inst_select_exp riscv_config 23 23 (Op Xor [Lookup CurrHeap; Const (7w:64 word)])``;
val _ = out "selector_prelude_load_offset" ``inst_select_exp riscv_config 23 23 (Load (Op Add [Var 18; Const (7w:64 word)]))``;
val _ = out "selector_prelude_load_large_offset" ``inst_select_exp riscv_config 23 23 (Load (Op Add [Var 18; Const (4096w:64 word)]))``;
