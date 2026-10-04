val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "blastLib"; load "preamble"; load "riscv_stepTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_stepTheory;
val _ = computeLib.add_funs [Encode_def,Rtype_def,opc_def,Decode_def,boolify32_def,DecodeAny_def];
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
(* Generic kernel proof using the original native definitions, not a fixture. *)
val mulhu_decode = Q.prove(
  `!rd rs1 rs2. DecodeAny (Word (Encode (MulDiv (MULHU (rd,rs1,rs2))))) = MulDiv (MULHU (rd,rs1,rs2))`,
  rpt gen_tac >> simp [DecodeAny_def, Encode_def, Rtype_def, opc_def, Decode_def, boolify32_def] >>
  CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >> simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "mulhu_decode_universal="; print_term(concl mulhu_decode); print "\n");
val _ = print ("mulhu_decode_hypotheses=" ^ Int.toString(length(hyp mulhu_decode)) ^ "\n");
val mulhu_decode_zero = EVAL ``DecodeAny (Word (Encode (MulDiv (MULHU (0w,0w,0w))))) = MulDiv (MULHU (0w,0w,0w))``;
val _ = if aconv (rhs(concl mulhu_decode_zero)) T then () else raise Fail "mulhu_decode_zero";
val _ = (print "mulhu_decode_zero="; print_term(rhs(concl mulhu_decode_zero)); print "\n");
val mulhu_decode_all_ones = EVAL ``DecodeAny (Word (Encode (MulDiv (MULHU (31w,31w,31w))))) = MulDiv (MULHU (31w,31w,31w))``;
val _ = if aconv (rhs(concl mulhu_decode_all_ones)) T then () else raise Fail "mulhu_decode_all_ones";
val _ = (print "mulhu_decode_all_ones="; print_term(rhs(concl mulhu_decode_all_ones)); print "\n");
val mulhu_decode_high_bit = EVAL ``DecodeAny (Word (Encode (MulDiv (MULHU (1w,0w,16w))))) = MulDiv (MULHU (1w,0w,16w))``;
val _ = if aconv (rhs(concl mulhu_decode_high_bit)) T then () else raise Fail "mulhu_decode_high_bit";
val _ = (print "mulhu_decode_high_bit="; print_term(rhs(concl mulhu_decode_high_bit)); print "\n");
val mulhu_decode_alias = EVAL ``DecodeAny (Word (Encode (MulDiv (MULHU (7w,7w,7w))))) = MulDiv (MULHU (7w,7w,7w))``;
val _ = if aconv (rhs(concl mulhu_decode_alias)) T then () else raise Fail "mulhu_decode_alias";
val _ = (print "mulhu_decode_alias="; print_term(rhs(concl mulhu_decode_alias)); print "\n");
val mulhu_term = ``Encode (MulDiv (MULHU (rdv,rs1v,rs2v)))``;
val mulhu_source = SIMP_CONV (srw_ss()) [Encode_def] mulhu_term;
val _ = (print "mulhu_encode_source_clause="; print_term(concl mulhu_source); print "\n");
val _ = print ("mulhu_carrier_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars mulhu_term)) ^ "\n");
(* Generic kernel proof using the original native definitions, not a fixture. *)
val mul_decode = Q.prove(
  `!rd rs1 rs2. DecodeAny (Word (Encode (MulDiv (MUL (rd,rs1,rs2))))) = MulDiv (MUL (rd,rs1,rs2))`,
  rpt gen_tac >> simp [DecodeAny_def, Encode_def, Rtype_def, opc_def, Decode_def, boolify32_def] >>
  CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >> simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "mul_decode_universal="; print_term(concl mul_decode); print "\n");
val _ = print ("mul_decode_hypotheses=" ^ Int.toString(length(hyp mul_decode)) ^ "\n");
val mul_decode_zero = EVAL ``DecodeAny (Word (Encode (MulDiv (MUL (0w,0w,0w))))) = MulDiv (MUL (0w,0w,0w))``;
val _ = if aconv (rhs(concl mul_decode_zero)) T then () else raise Fail "mul_decode_zero";
val _ = (print "mul_decode_zero="; print_term(rhs(concl mul_decode_zero)); print "\n");
val mul_decode_all_ones = EVAL ``DecodeAny (Word (Encode (MulDiv (MUL (31w,31w,31w))))) = MulDiv (MUL (31w,31w,31w))``;
val _ = if aconv (rhs(concl mul_decode_all_ones)) T then () else raise Fail "mul_decode_all_ones";
val _ = (print "mul_decode_all_ones="; print_term(rhs(concl mul_decode_all_ones)); print "\n");
val mul_decode_high_bit = EVAL ``DecodeAny (Word (Encode (MulDiv (MUL (1w,0w,16w))))) = MulDiv (MUL (1w,0w,16w))``;
val _ = if aconv (rhs(concl mul_decode_high_bit)) T then () else raise Fail "mul_decode_high_bit";
val _ = (print "mul_decode_high_bit="; print_term(rhs(concl mul_decode_high_bit)); print "\n");
val mul_decode_alias = EVAL ``DecodeAny (Word (Encode (MulDiv (MUL (7w,7w,7w))))) = MulDiv (MUL (7w,7w,7w))``;
val _ = if aconv (rhs(concl mul_decode_alias)) T then () else raise Fail "mul_decode_alias";
val _ = (print "mul_decode_alias="; print_term(rhs(concl mul_decode_alias)); print "\n");
val mul_term = ``Encode (MulDiv (MUL (rdv,rs1v,rs2v)))``;
val mul_source = SIMP_CONV (srw_ss()) [Encode_def] mul_term;
val _ = (print "mul_encode_source_clause="; print_term(concl mul_source); print "\n");
val _ = print ("mul_carrier_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars mul_term)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
