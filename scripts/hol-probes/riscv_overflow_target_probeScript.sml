load "preamble"; load "bitstringLib"; load "riscvTheory"; load "riscv_targetTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_targetTheory;
val _ = Globals.linewidth := 100000;
fun riscv_type s = Type.mk_thy_type {Thy = "riscv", Tyop = s, Args = []};
val riscv_tys = List.map riscv_type
  ["instruction", "Shift", "ArithI", "ArithR", "MulDiv", "Branch", "Load", "Store"];
val riscv_bytes_conv = computeLib.compset_conv (wordsLib.words_compset)
  [computeLib.Defs [riscv_enc_def, riscv_ast_def, riscv_encode_def, riscv_const32_def,
    riscv_bop_r_def, riscv_bop_i_def, riscv_sh_def, riscv_memop_def,
    Encode_def, opc_def, Itype_def, Rtype_def, Stype_def, SBtype_def, Utype_def, UJtype_def],
   computeLib.Convs [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
   computeLib.Tys ([sumSyntax.mk_sum(alpha,beta),
     mk_thy_type{Thy="asm",Tyop="cmp",Args=[]}] @ riscv_tys),
   computeLib.Extenders [pairLib.add_pair_compset]];
fun out label q = (print (label ^ "="); print_term (rconc ((REWRITE_CONV [riscv_enc_def] THENC EVAL THENC riscv_bytes_conv) q)); print "\n");
val _ = out "overflow_add_ast_0" ``riscv_ast (Inst (Arith (AddOverflow 5 2 3 4)) :64 asm)``;
val _ = out "overflow_add_enc_0" ``riscv_enc (Inst (Arith (AddOverflow 5 2 3 4)) :64 asm)``;
val _ = out "overflow_sub_ast_0" ``riscv_ast (Inst (Arith (SubOverflow 5 2 3 4)) :64 asm)``;
val _ = out "overflow_sub_enc_0" ``riscv_enc (Inst (Arith (SubOverflow 5 2 3 4)) :64 asm)``;
val _ = out "overflow_add_ast_1" ``riscv_ast (Inst (Arith (AddOverflow 0 0 0 0)) :64 asm)``;
val _ = out "overflow_add_enc_1" ``riscv_enc (Inst (Arith (AddOverflow 0 0 0 0)) :64 asm)``;
val _ = out "overflow_sub_ast_1" ``riscv_ast (Inst (Arith (SubOverflow 0 0 0 0)) :64 asm)``;
val _ = out "overflow_sub_enc_1" ``riscv_enc (Inst (Arith (SubOverflow 0 0 0 0)) :64 asm)``;
val _ = out "overflow_add_ast_2" ``riscv_ast (Inst (Arith (AddOverflow 31 31 31 31)) :64 asm)``;
val _ = out "overflow_add_enc_2" ``riscv_enc (Inst (Arith (AddOverflow 31 31 31 31)) :64 asm)``;
val _ = out "overflow_sub_ast_2" ``riscv_ast (Inst (Arith (SubOverflow 31 31 31 31)) :64 asm)``;
val _ = out "overflow_sub_enc_2" ``riscv_enc (Inst (Arith (SubOverflow 31 31 31 31)) :64 asm)``;
val _ = out "overflow_add_ast_3" ``riscv_ast (Inst (Arith (AddOverflow 30 29 28 27)) :64 asm)``;
val _ = out "overflow_add_enc_3" ``riscv_enc (Inst (Arith (AddOverflow 30 29 28 27)) :64 asm)``;
val _ = out "overflow_sub_ast_3" ``riscv_ast (Inst (Arith (SubOverflow 30 29 28 27)) :64 asm)``;
val _ = out "overflow_sub_enc_3" ``riscv_enc (Inst (Arith (SubOverflow 30 29 28 27)) :64 asm)``;
val _ = out "overflow_add_ast_4" ``riscv_ast (Inst (Arith (AddOverflow 5 2 5 4)) :64 asm)``;
val _ = out "overflow_add_enc_4" ``riscv_enc (Inst (Arith (AddOverflow 5 2 5 4)) :64 asm)``;
val _ = out "overflow_sub_ast_4" ``riscv_ast (Inst (Arith (SubOverflow 5 2 5 4)) :64 asm)``;
val _ = out "overflow_sub_enc_4" ``riscv_enc (Inst (Arith (SubOverflow 5 2 5 4)) :64 asm)``;
val _ = out "overflow_add_ast_5" ``riscv_ast (Inst (Arith (AddOverflow 4 2 3 4)) :64 asm)``;
val _ = out "overflow_add_enc_5" ``riscv_enc (Inst (Arith (AddOverflow 4 2 3 4)) :64 asm)``;
val _ = out "overflow_sub_ast_5" ``riscv_ast (Inst (Arith (SubOverflow 4 2 3 4)) :64 asm)``;
val _ = out "overflow_sub_enc_5" ``riscv_enc (Inst (Arith (SubOverflow 4 2 3 4)) :64 asm)``;
val _ = out "overflow_add_ast_6" ``riscv_ast (Inst (Arith (AddOverflow 2 2 3 4)) :64 asm)``;
val _ = out "overflow_add_enc_6" ``riscv_enc (Inst (Arith (AddOverflow 2 2 3 4)) :64 asm)``;
val _ = out "overflow_sub_ast_6" ``riscv_ast (Inst (Arith (SubOverflow 2 2 3 4)) :64 asm)``;
val _ = out "overflow_sub_enc_6" ``riscv_enc (Inst (Arith (SubOverflow 2 2 3 4)) :64 asm)``;
val _ = out "overflow_add_ast_7" ``riscv_ast (Inst (Arith (AddOverflow 5 2 3 31)) :64 asm)``;
val _ = out "overflow_add_enc_7" ``riscv_enc (Inst (Arith (AddOverflow 5 2 3 31)) :64 asm)``;
val _ = out "overflow_sub_ast_7" ``riscv_ast (Inst (Arith (SubOverflow 5 2 3 31)) :64 asm)``;
val _ = out "overflow_sub_enc_7" ``riscv_enc (Inst (Arith (SubOverflow 5 2 3 31)) :64 asm)``;
