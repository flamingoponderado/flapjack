(* Original compile_prog frame projection only. No allocator, ABI, body-output,
   or codec-success claim follows from these finite observations. *)
load "bossLib"; load "preamble"; load "word_to_stackTheory";
open HolKernel Parse bossLib preamble word_to_stackTheory;
fun print_eval label q =
  (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");
val config = ``(<| ISA := RISC_V; encode := ARB; big_endian := F;
  code_alignment := 0; link_reg := SOME 1; avoid_regs := [0;2;3;4;31];
  reg_count := 32; fp_reg_count := 0; two_reg_arith := F; valid_imm := ARB;
  addr_offset := ARB; hw_offset := ARB; byte_offset := ARB; jump_offset := ARB;
  cjump_offset := ARB; loc_offset := ARB |>) : 64 asm_config``;
val bitmaps = ``((List [],0n) : (64 word) app_list # num)``;
val _ = print_eval "retained_frame_empty"
  ``FST (SND (compile_prog ^config F (Skip:64 wordLang$prog) 0 22 ^bitmaps))``;
val _ = print_eval "retained_frame_register_edge"
  ``FST (SND (compile_prog ^config F (Assign 42 (Const (0w:64 word))) 22 22 ^bitmaps))``;
val _ = print_eval "retained_frame_first_spill"
  ``FST (SND (compile_prog ^config F (Assign 44 (Const (0w:64 word))) 0 22 ^bitmaps))``;
val _ = print_eval "retained_frame_second_spill"
  ``FST (SND (compile_prog ^config F (Assign 46 (Const (0w:64 word))) 0 22 ^bitmaps))``;
val _ = print_eval "retained_frame_args_dominate"
  ``FST (SND (compile_prog ^config F (Assign 44 (Const (0w:64 word))) 26 22 ^bitmaps))``;
val _ = print_eval "retained_frame_equal_demand"
  ``FST (SND (compile_prog ^config F (Assign 46 (Const (0w:64 word))) 24 22 ^bitmaps))``;
val _ = print_eval "retained_frame_zero_registers"
  ``FST (SND (compile_prog ^config F (Skip:64 wordLang$prog) 0 0 ^bitmaps))``;
val _ = print_eval "retained_frame_large_name"
  ``FST (SND (compile_prog ^config F (Assign 18446744073709551616 (Const (0w:64 word))) 0 22 ^bitmaps))``;
