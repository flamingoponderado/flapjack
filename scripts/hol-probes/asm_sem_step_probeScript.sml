(* Original-HOL oracle for asmSem inst_def, jump_to_offset_def, asm_def and asm_step_def
   (asmSemScript.sml:225-258): asm on every assembly clause and the instruction clauses on an
   8-bit state (LOG2 values for the Load8 count proved from LOG_UNIQUE, LOG2 being [nocompute]),
   and the HOL-proved projection of asm_step onto its transition and non-failure conjuncts. *)
load "bossLib";
load "preamble";
load "asmSemTheory";
open bossLib; open HolKernel Parse; open preamble;
open asmSemTheory;
val _ = Globals.linewidth := 4000;
fun lg tm = prove (tm, REWRITE_TAC [bitTheory.LOG2_def] >> irule logrootTheory.LOG_UNIQUE >> EVAL_TAC);
val log2_1 = lg ``LOG2 1 = 0``;
val conv = EVAL THENC REWRITE_CONV [log2_1] THENC EVAL;
fun observe label tm = (print (label ^ "="); print_term (rconc (conv tm)); print "\n");
val st = ``(<| regs := (\r. if r = 3 then (0xABw:8 word) else (0w:8 word));
             fp_regs := (\r. (0w:64 word));
             mem := (\x. if x = (0w:8 word) then (0x11w:8 word) else if x = (1w:8 word) then (0x22w:8 word) else (0x33w:8 word));
             mem_domain := {(0w:8 word); (1w:8 word); (2w:8 word); (3w:8 word)};
             pc := (2w:8 word); lr := 7; align := 0; be := F; failed := F |>): 8 asm_state``;
val _ = observe "as_skip_pc" ``(asm (Inst Skip) (9w:8 word) ^st).pc``;
val _ = observe "as_const" ``((asm (Inst (Const 2 (5w:8 word))) 9w ^st).regs 2, (asm (Inst (Const 2 (5w:8 word))) 9w ^st).pc)``;
val _ = observe "as_arith" ``(asm (Inst (Arith (Binop Add 2 3 (Imm (1w:8 word))))) 9w ^st).regs 2``;
val _ = observe "as_mem" ``((asm (Inst (Mem Load8 4 (Addr 0 (1w:8 word)))) 9w ^st).regs 4, (asm (Inst (Mem Load8 4 (Addr 0 (1w:8 word)))) 9w ^st).failed)``;
val _ = observe "as_jump" ``(asm (Jump (4w:8 word)) 9w ^st).pc``;
val _ = observe "as_jcmp_t" ``(asm (JumpCmp Equal 3 (Imm (0xABw:8 word)) 4w) 9w ^st).pc``;
val _ = observe "as_jcmp_f" ``(asm (JumpCmp Equal 3 (Imm (0w:8 word)) 4w) 9w ^st).pc``;
val _ = observe "as_call" ``((asm (Call (4w:8 word)) 9w ^st).regs 7, (asm (Call (4w:8 word)) 9w ^st).pc)``;
val _ = observe "as_jumpreg_ok" ``((asm (JumpReg 3) (9w:8 word) ^st).pc, (asm (JumpReg 3) (9w:8 word) ^st).failed)``;
val _ = observe "as_jumpreg_bad" ``(asm (JumpReg 3) (9w:8 word) (^st with align := 2)).failed``;
val _ = observe "as_loc" ``((asm (Loc 5 (3w:8 word)) 9w ^st).regs 5, (asm (Loc 5 (3w:8 word)) 9w ^st).pc)``;
val _ = (print "as_step_proj="; print_term (concl (prove (``asm_step c s1 i s2 ==>
    asm i (s1.pc + n2w (LENGTH (c.encode i))) s1 = s2 /\ ~s2.failed``, simp [asm_step_def]))); print "\n");
