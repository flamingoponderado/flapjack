(* Original-HOL oracle for the generic asmSem memory wrappers mem_load_def, mem_store_def and
   mem_op_def (asmSemScript.sml:191-226) on 8-bit states. LOG2 is [nocompute], so its positive
   values are proved from LOG_UNIQUE and rewritten between EVAL passes; the zero-count row keeps
   the unconstrained LOG2 0 symbolic, as the specification leaves it. *)
load "bossLib";
load "preamble";
load "asmSemTheory";
open bossLib; open HolKernel Parse; open preamble;
open asmSemTheory;
val _ = Globals.linewidth := 4000;
fun lg tm = prove (tm, REWRITE_TAC [bitTheory.LOG2_def] >> irule logrootTheory.LOG_UNIQUE >> EVAL_TAC);
val log2_1 = lg ``LOG2 1 = 0``;
val log2_2 = lg ``LOG2 2 = 1``;
val log2_4 = lg ``LOG2 4 = 2``;
val conv = EVAL THENC REWRITE_CONV [log2_1, log2_2, log2_4] THENC EVAL;
fun observe label tm = (print (label ^ "="); print_term (rconc (conv tm)); print "\n");
val st = ``(<| regs := (\r. if r = 3 then (0xABw:8 word) else (0w:8 word));
             fp_regs := (\r. (0w:64 word));
             mem := (\x. if x = (0w:8 word) then (0x11w:8 word) else if x = (1w:8 word) then (0x22w:8 word) else (0x33w:8 word));
             mem_domain := {(0w:8 word); (1w:8 word); (2w:8 word); (3w:8 word)};
             pc := (0w:8 word); lr := 0; align := 0; be := F; failed := F |>): 8 asm_state``;
val _ = observe "mo_ld2_le_reg" ``(mem_load 2 5 (Addr 0 (0w:8 word)) ^st).regs 5``;
val _ = observe "mo_ld2_le_ok" ``(mem_load 2 5 (Addr 0 (0w:8 word)) ^st).failed``;
val _ = observe "mo_ld2_be_reg" ``(mem_load 2 5 (Addr 0 (0w:8 word)) (^st with be := T)).regs 5``;
val _ = observe "mo_ld2_misaligned" ``(mem_load 2 5 (Addr 0 (1w:8 word)) ^st).failed``;
val _ = observe "mo_ld2_dom" ``(mem_load 2 5 (Addr 0 (6w:8 word)) ^st).failed``;
val _ = observe "mo_ld0_reg" ``(mem_load 0 5 (Addr 0 (1w:8 word)) ^st).regs 5``;
val _ = (print "mo_ld0_failed="; print_term (concl (prove (``(mem_load 0 5 (Addr 0 (1w:8 word)) ^st).failed <=> ~aligned (LOG2 0) (1w:8 word)``,
  simp [mem_load_def, read_mem_word_def, addr_def, read_reg_def, upd_reg_def, assert_def]))); print "\n");
val _ = observe "mo_st1_mem" ``(mem_store 1 3 (Addr 0 (2w:8 word)) ^st).mem 2w``;
val _ = observe "mo_st1_ok" ``(mem_store 1 3 (Addr 0 (2w:8 word)) ^st).failed``;
val _ = observe "mo_st2_misaligned" ``(mem_store 2 3 (Addr 0 (1w:8 word)) ^st).failed``;
val _ = observe "mo_op_load" ``(mem_op Load 5 (Addr 0 (1w:8 word)) ^st).regs 5``;
val _ = observe "mo_op_load32_failed" ``(mem_op Load32 5 (Addr 0 (0w:8 word)) ^st).failed``;
val _ = observe "mo_op_store8_mem" ``(mem_op Store8 3 (Addr 0 (1w:8 word)) ^st).mem 1w``;
val _ = observe "mo_op_load16_reg" ``(mem_op Load16 5 (Addr 0 (2w:8 word)) ^st).regs 5``;
