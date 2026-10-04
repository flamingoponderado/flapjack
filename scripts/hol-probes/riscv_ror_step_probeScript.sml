load "preamble"; load "riscv_stepTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_stepTheory;
val _ = Globals.linewidth := 1000000;
fun capture label defs tm = let val th = SIMP_CONV (srw_ss()) defs tm in
 (print(label ^ "_clause="); print_term(concl th); print "\n";
 print(label ^ "_types="); print(String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars tm))); print "\n";
 print(label ^ "_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n")) end;
val _ = capture "ror_run_srli" [Run_def, dfn'SRLI_def] ``Run (riscv$Shift (SRLI (rdv,rs1v,amtv))) ms``;
val _ = capture "ror_run_sll" [Run_def, dfn'SLL_def] ``Run (riscv$Shift (SLL (rdv,rs1v,rs2v))) ms``;
val _ = capture "ror_run_srl" [Run_def, dfn'SRL_def] ``Run (riscv$Shift (SRL (rdv,rs1v,rs2v))) ms``;
val _ = capture "ror_run_sub" [Run_def, dfn'SUB_def] ``Run (riscv$ArithR (SUB (rdv,rs1v,rs2v))) ms``;
val _ = computeLib.add_funs [Encode_def, Itype_def, Rtype_def, opc_def];
fun out label tm = let val th = EVAL tm val rhs = rhs(concl th) in
 if null(hyp th) andalso aconv rhs ``T`` then (print(label ^ "="); print_term rhs; print "\n")
 else raise Fail ("nontrue native instruction width: " ^ label) end;
val _ = out "ror_next_srli_zero" ``((Encode (Shift (SRLI (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "ror_next_srli_all_ones" ``((Encode (Shift (SRLI (5w,6w,63w)))) && (3w:word32)) = 3w``;
val _ = out "ror_next_sll_zero" ``((Encode (Shift (SLL (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "ror_next_sll_all_ones" ``((Encode (Shift (SLL (5w,6w,31w)))) && (3w:word32)) = 3w``;
val _ = out "ror_next_srl_zero" ``((Encode (Shift (SRL (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "ror_next_srl_all_ones" ``((Encode (Shift (SRL (5w,6w,31w)))) && (3w:word32)) = 3w``;
val _ = out "ror_next_sub_zero" ``((Encode (ArithR (SUB (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "ror_next_sub_all_ones" ``((Encode (ArithR (SUB (5w,6w,31w)))) && (3w:word32)) = 3w``;
val _ = OS.Process.exit OS.Process.success;
