(* Original word_alloc ssa_cc_trans_inst and ssa_cc_trans_exp at 64-bit and
   32-bit words (the FPMovToReg/FPMovFromReg dimindex branches). CakeML
   remains read-only; sparse trees print raw. *)
load "bossLib";
load "wordsLib";
load "word_allocTheory";
open HolKernel Parse boolLib bossLib word_allocTheory;
val _ = Globals.linewidth := 1000;
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val m = ``insert 2 10 (insert 3 11 (insert 4 12 LN)) : num num_map``;
val _ = observe "sti_skip" ``ssa_cc_trans_inst (Skip : 64 inst) ^m 21``;
val _ = observe "sti_const" ``ssa_cc_trans_inst (Const 2 (5w : 64 word)) ^m 21``;
val _ = observe "sti_binop_reg" ``ssa_cc_trans_inst (Arith (Binop Add 2 3 (Reg 4)) : 64 inst) ^m 21``;
val _ = observe "sti_binop_imm" ``ssa_cc_trans_inst (Arith (Binop Sub 2 9 (Imm 7w)) : 64 inst) ^m 21``;
val _ = observe "sti_shift_reg" ``ssa_cc_trans_inst (Arith (Shift Lsl 2 3 (Reg 4)) : 64 inst) ^m 21``;
val _ = observe "sti_shift_imm" ``ssa_cc_trans_inst (Arith (Shift Asr 2 3 (Imm 1w)) : 64 inst) ^m 21``;
val _ = observe "sti_div" ``ssa_cc_trans_inst (Arith (Div 2 3 4) : 64 inst) ^m 21``;
val _ = observe "sti_addcarry" ``ssa_cc_trans_inst (Arith (AddCarry 2 3 4 5) : 64 inst) ^m 21``;
val _ = observe "sti_addoverflow" ``ssa_cc_trans_inst (Arith (AddOverflow 2 3 4 5) : 64 inst) ^m 21``;
val _ = observe "sti_suboverflow" ``ssa_cc_trans_inst (Arith (SubOverflow 2 3 4 5) : 64 inst) ^m 21``;
val _ = observe "sti_longmul" ``ssa_cc_trans_inst (Arith (LongMul 2 3 4 9) : 64 inst) ^m 21``;
val _ = observe "sti_longdiv" ``ssa_cc_trans_inst (Arith (LongDiv 2 3 4 9 3) : 64 inst) ^m 21``;
val _ = observe "sti_load" ``ssa_cc_trans_inst (Mem Load 2 (Addr 3 8w) : 64 inst) ^m 21``;
val _ = observe "sti_store" ``ssa_cc_trans_inst (Mem Store 2 (Addr 3 8w) : 64 inst) ^m 21``;
val _ = observe "sti_load32" ``ssa_cc_trans_inst (Mem Load32 4 (Addr 9 0w) : 64 inst) ^m 21``;
val _ = observe "sti_store8" ``ssa_cc_trans_inst (Mem Store8 9 (Addr 4 1w) : 64 inst) ^m 21``;
val _ = observe "sti_load16" ``ssa_cc_trans_inst (Mem Load16 2 (Addr 3 8w) : 64 inst) ^m 21``;
val _ = observe "sti_fpless" ``ssa_cc_trans_inst (FP (FPLess 2 1 0) : 64 inst) ^m 21``;
val _ = observe "sti_fpadd" ``ssa_cc_trans_inst (FP (FPAdd 2 1 0) : 64 inst) ^m 21``;
val _ = observe "sti_movto64" ``ssa_cc_trans_inst (FP (FPMovToReg 2 3 1) : 64 inst) ^m 21``;
val _ = observe "sti_movto32" ``ssa_cc_trans_inst (FP (FPMovToReg 2 3 1) : 32 inst) ^m 21``;
val _ = observe "sti_movfrom64" ``ssa_cc_trans_inst (FP (FPMovFromReg 1 2 3) : 64 inst) ^m 21``;
val _ = observe "sti_movfrom32_distinct" ``ssa_cc_trans_inst (FP (FPMovFromReg 1 2 3) : 32 inst) ^m 21``;
val _ = observe "sti_movfrom32_same" ``ssa_cc_trans_inst (FP (FPMovFromReg 1 2 2) : 32 inst) ^m 21``;
val _ = observe "ste_var" ``ssa_cc_trans_exp ^m (Var 3 : 64 wordLang$exp)``;
val _ = observe "ste_missing" ``ssa_cc_trans_exp ^m (Var 9 : 64 wordLang$exp)``;
val _ = observe "ste_nested" ``ssa_cc_trans_exp ^m (Op Add [Var 2; Load (Var 4); Const 3w; Shift Lsr (Var 3) (Var 2)] : 64 wordLang$exp)``;
val _ = observe "ste_lookup" ``ssa_cc_trans_exp ^m (Lookup NextFree : 64 wordLang$exp)``;
