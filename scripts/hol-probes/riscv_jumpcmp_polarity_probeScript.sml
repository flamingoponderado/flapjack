(* Original executed JumpCmp byte observations; conditions are literal HOL
   predicates. Short/long and register/immediate/Test paths are independent. *)
load "bossLib";
load "preamble";
open bossLib HolKernel Parse preamble;
val _ = Globals.linewidth := 10000;
load "bitstringLib";
load "riscvTheory";
load "riscv_targetTheory";
open riscvTheory riscv_targetTheory;
fun riscv_type s = Type.mk_thy_type {Thy = "riscv", Tyop = s, Args = []};
val riscv_tys =
  List.map riscv_type
    ["instruction", "Shift", "ArithI", "ArithR", "MulDiv", "Branch",
     "Load", "Store"];
val riscv_bytes_conv =
  computeLib.compset_conv (wordsLib.words_compset)
    [computeLib.Defs
      [riscv_ast_def, riscv_encode_def, riscv_const32_def,
       riscv_bop_r_def, riscv_bop_i_def, riscv_sh_def, riscv_memop_def,
       Encode_def, opc_def, Itype_def, Rtype_def, Stype_def, SBtype_def,
       Utype_def, UJtype_def],
     computeLib.Convs
       [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
     computeLib.Tys
       ([sumSyntax.mk_sum(alpha,beta),
         mk_thy_type{Thy="asm",Tyop="cmp",Args=[]}] @ riscv_tys),
     computeLib.Extenders [pairLib.add_pair_compset]];
val _ = print ("branch_equal_reg_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Equal 1 (Reg 2) 16w))))``)) ^ "\n");
val _ = print ("branch_equal_reg_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Equal 1 (Reg 2) 8192w))))``)) ^ "\n");
val _ = print ("branch_equal_imm_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Equal 1 (Imm 7w) 16w))))``)) ^ "\n");
val _ = print ("branch_equal_imm_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Equal 1 (Imm 7w) 8192w))))``)) ^ "\n");
val _ = print ("branch_notequal_reg_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotEqual 1 (Reg 2) 16w))))``)) ^ "\n");
val _ = print ("branch_notequal_reg_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotEqual 1 (Reg 2) 8192w))))``)) ^ "\n");
val _ = print ("branch_notequal_imm_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotEqual 1 (Imm 7w) 16w))))``)) ^ "\n");
val _ = print ("branch_notequal_imm_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotEqual 1 (Imm 7w) 8192w))))``)) ^ "\n");
val _ = print ("branch_less_reg_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Less 1 (Reg 2) 16w))))``)) ^ "\n");
val _ = print ("branch_less_reg_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Less 1 (Reg 2) 8192w))))``)) ^ "\n");
val _ = print ("branch_less_imm_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Less 1 (Imm 7w) 16w))))``)) ^ "\n");
val _ = print ("branch_less_imm_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Less 1 (Imm 7w) 8192w))))``)) ^ "\n");
val _ = print ("branch_notless_reg_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotLess 1 (Reg 2) 16w))))``)) ^ "\n");
val _ = print ("branch_notless_reg_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotLess 1 (Reg 2) 8192w))))``)) ^ "\n");
val _ = print ("branch_notless_imm_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotLess 1 (Imm 7w) 16w))))``)) ^ "\n");
val _ = print ("branch_notless_imm_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotLess 1 (Imm 7w) 8192w))))``)) ^ "\n");
val _ = print ("branch_lower_reg_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Lower 1 (Reg 2) 16w))))``)) ^ "\n");
val _ = print ("branch_lower_reg_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Lower 1 (Reg 2) 8192w))))``)) ^ "\n");
val _ = print ("branch_lower_imm_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Lower 1 (Imm 7w) 16w))))``)) ^ "\n");
val _ = print ("branch_lower_imm_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Lower 1 (Imm 7w) 8192w))))``)) ^ "\n");
val _ = print ("branch_notlower_reg_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotLower 1 (Reg 2) 16w))))``)) ^ "\n");
val _ = print ("branch_notlower_reg_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotLower 1 (Reg 2) 8192w))))``)) ^ "\n");
val _ = print ("branch_notlower_imm_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotLower 1 (Imm 7w) 16w))))``)) ^ "\n");
val _ = print ("branch_notlower_imm_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotLower 1 (Imm 7w) 8192w))))``)) ^ "\n");
val _ = print ("branch_test_reg_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Test 1 (Reg 2) 16w))))``)) ^ "\n");
val _ = print ("branch_test_reg_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Test 1 (Reg 2) 8192w))))``)) ^ "\n");
val _ = print ("branch_test_imm_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Test 1 (Imm 7w) 16w))))``)) ^ "\n");
val _ = print ("branch_test_imm_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp Test 1 (Imm 7w) 8192w))))``)) ^ "\n");
val _ = print ("branch_nottest_reg_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotTest 1 (Reg 2) 16w))))``)) ^ "\n");
val _ = print ("branch_nottest_reg_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotTest 1 (Reg 2) 8192w))))``)) ^ "\n");
val _ = print ("branch_nottest_imm_short=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotTest 1 (Imm 7w) 16w))))``)) ^ "\n");
val _ = print ("branch_nottest_imm_long=" ^ term_to_string (rconc (riscv_bytes_conv ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (JumpCmp NotTest 1 (Imm 7w) 8192w))))``)) ^ "\n");
