(* Universal derived source-clause relations; no opcode is chosen for an unspecified slot. *)
load "preamble";
load "riscv_targetTheory";
open HolKernel Parse bossLib;
open preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;
val binop = prove(
 ``!b r1 r2 (i:word64).
    riscv_ast (Inst (Arith (Binop b r1 r2 (Imm i)))) =
    if b = Sub then [ArithI (ADDI (n2w r1,n2w r2,-(w2w i)))]
    else [ArithI (riscv_bop_i b (n2w r1,n2w r2,w2w i))]``,
 rpt GEN_TAC >> Cases_on `b` >> simp [riscv_ast_def,riscv_bop_i_def]);
val _ = if null (hyp binop) then () else raise Fail "helper acquired assumptions";
val _ = print "helper_binop_statement=";
val _ = print_term (concl binop);
val _ = print "\n";
val _ = print "helper_binop_hypotheses=";
val _ = print (Int.toString (length (hyp binop)) ^ "\n");
val _ = print "helper_binop_proved=";
val _ = print_term (rhs (concl (EQT_INTRO binop)));
val _ = print "\n";
val shift_imm = prove(
 ``!sh r1 r2 (i:word64).
    riscv_ast (Inst (Arith (Shift sh r1 r2 (Imm i)))) =
    if sh = Ror then
      [Shift (SRLI (31w,n2w r2,n2w (w2n i)));
       Shift (SLLI (n2w r1,n2w r2,n2w (64-w2n i)));
       ArithR (OR (n2w r1,n2w r1,31w))]
    else [Shift (riscv_sh sh (n2w r1,n2w r2,n2w (w2n i)))]``,
 rpt GEN_TAC >> Cases_on `sh` >> simp [riscv_ast_def,riscv_sh_def]);
val _ = if null (hyp shift_imm) then () else raise Fail "helper acquired assumptions";
val _ = print "helper_shift_imm_statement=";
val _ = print_term (concl shift_imm);
val _ = print "\n";
val _ = print "helper_shift_imm_hypotheses=";
val _ = print (Int.toString (length (hyp shift_imm)) ^ "\n");
val _ = print "helper_shift_imm_proved=";
val _ = print_term (rhs (concl (EQT_INTRO shift_imm)));
val _ = print "\n";
val shift_reg = prove(
 ``!sh r1 r2 r.
    riscv_ast (Inst (Arith (Shift sh r1 r2 (Reg r)))) =
    if sh = Ror then
      [ArithI (ORI (31w,0w,64w));ArithR (SUB (31w,31w,n2w r));
       Shift (SLL (31w,n2w r2,31w));Shift (SRL (n2w r1,n2w r2,n2w r));
       ArithR (OR (n2w r1,n2w r1,31w))]
    else [Shift (riscv_shv sh (n2w r1,n2w r2,n2w r))]``,
 rpt GEN_TAC >> Cases_on `sh` >> simp [riscv_ast_def,riscv_shv_def]);
val _ = if null (hyp shift_reg) then () else raise Fail "helper acquired assumptions";
val _ = print "helper_shift_reg_statement=";
val _ = print_term (concl shift_reg);
val _ = print "\n";
val _ = print "helper_shift_reg_hypotheses=";
val _ = print (Int.toString (length (hyp shift_reg)) ^ "\n");
val _ = print "helper_shift_reg_proved=";
val _ = print_term (rhs (concl (EQT_INTRO shift_reg)));
val _ = print "\n";
val _ = OS.Process.exit OS.Process.success;
