val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "blastLib"; load "preamble"; load "riscv_stepTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_stepTheory;
val defs = [Encode_def,SBtype_def,opc_def,Decode_def,boolify32_def,DecodeAny_def,asImm12_def];
val _ = computeLib.add_funs defs;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val beq_decode = Q.prove(
  `!rs1 rs2 imm. DecodeAny (Word (Encode (Branch (BEQ (rs1,rs2,imm))))) = Branch (BEQ (rs1,rs2,imm))`,
  rpt gen_tac >> simp defs >> CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >>
  simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "beq_decode_universal="; print_term (concl beq_decode); print "\n");
val _ = print ("beq_decode_hypotheses=" ^ Int.toString (length (hyp beq_decode)) ^ "\n");
val beq_zero = EVAL ``DecodeAny (Word (Encode (Branch (BEQ (0w,0w,0w))))) = Branch (BEQ (0w,0w,0w))``;
val _ = if aconv (rhs (concl beq_zero)) T then () else raise Fail "beq_zero";
val _ = (print "beq_zero="; print_term (rhs (concl beq_zero)); print "\n");
val beq_all_ones = EVAL ``DecodeAny (Word (Encode (Branch (BEQ (31w,31w,-1w))))) = Branch (BEQ (31w,31w,-1w))``;
val _ = if aconv (rhs (concl beq_all_ones)) T then () else raise Fail "beq_all_ones";
val _ = (print "beq_all_ones="; print_term (rhs (concl beq_all_ones)); print "\n");
val beq_alias_sign = EVAL ``DecodeAny (Word (Encode (Branch (BEQ (1w,1w,0x800w))))) = Branch (BEQ (1w,1w,0x800w))``;
val _ = if aconv (rhs (concl beq_alias_sign)) T then () else raise Fail "beq_alias_sign";
val _ = (print "beq_alias_sign="; print_term (rhs (concl beq_alias_sign)); print "\n");
val beq_mixed = EVAL ``DecodeAny (Word (Encode (Branch (BEQ (7w,16w,0x57Fw))))) = Branch (BEQ (7w,16w,0x57Fw))``;
val _ = if aconv (rhs (concl beq_mixed)) T then () else raise Fail "beq_mixed";
val _ = (print "beq_mixed="; print_term (rhs (concl beq_mixed)); print "\n");
val beq_term = ``Encode (Branch (BEQ (rs1v,rs2v,immv)))``;
val beq_source = SIMP_CONV (srw_ss()) [Encode_def] beq_term;
val _ = (print "beq_source_clause="; print_term (concl beq_source); print "\n");
val _ = print ("beq_carrier_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (free_vars beq_term)) ^ "\n");
val bne_decode = Q.prove(
  `!rs1 rs2 imm. DecodeAny (Word (Encode (Branch (BNE (rs1,rs2,imm))))) = Branch (BNE (rs1,rs2,imm))`,
  rpt gen_tac >> simp defs >> CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >>
  simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "bne_decode_universal="; print_term (concl bne_decode); print "\n");
val _ = print ("bne_decode_hypotheses=" ^ Int.toString (length (hyp bne_decode)) ^ "\n");
val bne_zero = EVAL ``DecodeAny (Word (Encode (Branch (BNE (0w,0w,0w))))) = Branch (BNE (0w,0w,0w))``;
val _ = if aconv (rhs (concl bne_zero)) T then () else raise Fail "bne_zero";
val _ = (print "bne_zero="; print_term (rhs (concl bne_zero)); print "\n");
val bne_all_ones = EVAL ``DecodeAny (Word (Encode (Branch (BNE (31w,31w,-1w))))) = Branch (BNE (31w,31w,-1w))``;
val _ = if aconv (rhs (concl bne_all_ones)) T then () else raise Fail "bne_all_ones";
val _ = (print "bne_all_ones="; print_term (rhs (concl bne_all_ones)); print "\n");
val bne_alias_sign = EVAL ``DecodeAny (Word (Encode (Branch (BNE (1w,1w,0x800w))))) = Branch (BNE (1w,1w,0x800w))``;
val _ = if aconv (rhs (concl bne_alias_sign)) T then () else raise Fail "bne_alias_sign";
val _ = (print "bne_alias_sign="; print_term (rhs (concl bne_alias_sign)); print "\n");
val bne_mixed = EVAL ``DecodeAny (Word (Encode (Branch (BNE (7w,16w,0x57Fw))))) = Branch (BNE (7w,16w,0x57Fw))``;
val _ = if aconv (rhs (concl bne_mixed)) T then () else raise Fail "bne_mixed";
val _ = (print "bne_mixed="; print_term (rhs (concl bne_mixed)); print "\n");
val bne_term = ``Encode (Branch (BNE (rs1v,rs2v,immv)))``;
val bne_source = SIMP_CONV (srw_ss()) [Encode_def] bne_term;
val _ = (print "bne_source_clause="; print_term (concl bne_source); print "\n");
val _ = print ("bne_carrier_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (free_vars bne_term)) ^ "\n");
val blt_decode = Q.prove(
  `!rs1 rs2 imm. DecodeAny (Word (Encode (Branch (BLT (rs1,rs2,imm))))) = Branch (BLT (rs1,rs2,imm))`,
  rpt gen_tac >> simp defs >> CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >>
  simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "blt_decode_universal="; print_term (concl blt_decode); print "\n");
val _ = print ("blt_decode_hypotheses=" ^ Int.toString (length (hyp blt_decode)) ^ "\n");
val blt_zero = EVAL ``DecodeAny (Word (Encode (Branch (BLT (0w,0w,0w))))) = Branch (BLT (0w,0w,0w))``;
val _ = if aconv (rhs (concl blt_zero)) T then () else raise Fail "blt_zero";
val _ = (print "blt_zero="; print_term (rhs (concl blt_zero)); print "\n");
val blt_all_ones = EVAL ``DecodeAny (Word (Encode (Branch (BLT (31w,31w,-1w))))) = Branch (BLT (31w,31w,-1w))``;
val _ = if aconv (rhs (concl blt_all_ones)) T then () else raise Fail "blt_all_ones";
val _ = (print "blt_all_ones="; print_term (rhs (concl blt_all_ones)); print "\n");
val blt_alias_sign = EVAL ``DecodeAny (Word (Encode (Branch (BLT (1w,1w,0x800w))))) = Branch (BLT (1w,1w,0x800w))``;
val _ = if aconv (rhs (concl blt_alias_sign)) T then () else raise Fail "blt_alias_sign";
val _ = (print "blt_alias_sign="; print_term (rhs (concl blt_alias_sign)); print "\n");
val blt_mixed = EVAL ``DecodeAny (Word (Encode (Branch (BLT (7w,16w,0x57Fw))))) = Branch (BLT (7w,16w,0x57Fw))``;
val _ = if aconv (rhs (concl blt_mixed)) T then () else raise Fail "blt_mixed";
val _ = (print "blt_mixed="; print_term (rhs (concl blt_mixed)); print "\n");
val blt_term = ``Encode (Branch (BLT (rs1v,rs2v,immv)))``;
val blt_source = SIMP_CONV (srw_ss()) [Encode_def] blt_term;
val _ = (print "blt_source_clause="; print_term (concl blt_source); print "\n");
val _ = print ("blt_carrier_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (free_vars blt_term)) ^ "\n");
val bltu_decode = Q.prove(
  `!rs1 rs2 imm. DecodeAny (Word (Encode (Branch (BLTU (rs1,rs2,imm))))) = Branch (BLTU (rs1,rs2,imm))`,
  rpt gen_tac >> simp defs >> CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >>
  simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "bltu_decode_universal="; print_term (concl bltu_decode); print "\n");
val _ = print ("bltu_decode_hypotheses=" ^ Int.toString (length (hyp bltu_decode)) ^ "\n");
val bltu_zero = EVAL ``DecodeAny (Word (Encode (Branch (BLTU (0w,0w,0w))))) = Branch (BLTU (0w,0w,0w))``;
val _ = if aconv (rhs (concl bltu_zero)) T then () else raise Fail "bltu_zero";
val _ = (print "bltu_zero="; print_term (rhs (concl bltu_zero)); print "\n");
val bltu_all_ones = EVAL ``DecodeAny (Word (Encode (Branch (BLTU (31w,31w,-1w))))) = Branch (BLTU (31w,31w,-1w))``;
val _ = if aconv (rhs (concl bltu_all_ones)) T then () else raise Fail "bltu_all_ones";
val _ = (print "bltu_all_ones="; print_term (rhs (concl bltu_all_ones)); print "\n");
val bltu_alias_sign = EVAL ``DecodeAny (Word (Encode (Branch (BLTU (1w,1w,0x800w))))) = Branch (BLTU (1w,1w,0x800w))``;
val _ = if aconv (rhs (concl bltu_alias_sign)) T then () else raise Fail "bltu_alias_sign";
val _ = (print "bltu_alias_sign="; print_term (rhs (concl bltu_alias_sign)); print "\n");
val bltu_mixed = EVAL ``DecodeAny (Word (Encode (Branch (BLTU (7w,16w,0x57Fw))))) = Branch (BLTU (7w,16w,0x57Fw))``;
val _ = if aconv (rhs (concl bltu_mixed)) T then () else raise Fail "bltu_mixed";
val _ = (print "bltu_mixed="; print_term (rhs (concl bltu_mixed)); print "\n");
val bltu_term = ``Encode (Branch (BLTU (rs1v,rs2v,immv)))``;
val bltu_source = SIMP_CONV (srw_ss()) [Encode_def] bltu_term;
val _ = (print "bltu_source_clause="; print_term (concl bltu_source); print "\n");
val _ = print ("bltu_carrier_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (free_vars bltu_term)) ^ "\n");
val bge_decode = Q.prove(
  `!rs1 rs2 imm. DecodeAny (Word (Encode (Branch (BGE (rs1,rs2,imm))))) = Branch (BGE (rs1,rs2,imm))`,
  rpt gen_tac >> simp defs >> CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >>
  simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "bge_decode_universal="; print_term (concl bge_decode); print "\n");
val _ = print ("bge_decode_hypotheses=" ^ Int.toString (length (hyp bge_decode)) ^ "\n");
val bge_zero = EVAL ``DecodeAny (Word (Encode (Branch (BGE (0w,0w,0w))))) = Branch (BGE (0w,0w,0w))``;
val _ = if aconv (rhs (concl bge_zero)) T then () else raise Fail "bge_zero";
val _ = (print "bge_zero="; print_term (rhs (concl bge_zero)); print "\n");
val bge_all_ones = EVAL ``DecodeAny (Word (Encode (Branch (BGE (31w,31w,-1w))))) = Branch (BGE (31w,31w,-1w))``;
val _ = if aconv (rhs (concl bge_all_ones)) T then () else raise Fail "bge_all_ones";
val _ = (print "bge_all_ones="; print_term (rhs (concl bge_all_ones)); print "\n");
val bge_alias_sign = EVAL ``DecodeAny (Word (Encode (Branch (BGE (1w,1w,0x800w))))) = Branch (BGE (1w,1w,0x800w))``;
val _ = if aconv (rhs (concl bge_alias_sign)) T then () else raise Fail "bge_alias_sign";
val _ = (print "bge_alias_sign="; print_term (rhs (concl bge_alias_sign)); print "\n");
val bge_mixed = EVAL ``DecodeAny (Word (Encode (Branch (BGE (7w,16w,0x57Fw))))) = Branch (BGE (7w,16w,0x57Fw))``;
val _ = if aconv (rhs (concl bge_mixed)) T then () else raise Fail "bge_mixed";
val _ = (print "bge_mixed="; print_term (rhs (concl bge_mixed)); print "\n");
val bge_term = ``Encode (Branch (BGE (rs1v,rs2v,immv)))``;
val bge_source = SIMP_CONV (srw_ss()) [Encode_def] bge_term;
val _ = (print "bge_source_clause="; print_term (concl bge_source); print "\n");
val _ = print ("bge_carrier_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (free_vars bge_term)) ^ "\n");
val bgeu_decode = Q.prove(
  `!rs1 rs2 imm. DecodeAny (Word (Encode (Branch (BGEU (rs1,rs2,imm))))) = Branch (BGEU (rs1,rs2,imm))`,
  rpt gen_tac >> simp defs >> CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >>
  simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "bgeu_decode_universal="; print_term (concl bgeu_decode); print "\n");
val _ = print ("bgeu_decode_hypotheses=" ^ Int.toString (length (hyp bgeu_decode)) ^ "\n");
val bgeu_zero = EVAL ``DecodeAny (Word (Encode (Branch (BGEU (0w,0w,0w))))) = Branch (BGEU (0w,0w,0w))``;
val _ = if aconv (rhs (concl bgeu_zero)) T then () else raise Fail "bgeu_zero";
val _ = (print "bgeu_zero="; print_term (rhs (concl bgeu_zero)); print "\n");
val bgeu_all_ones = EVAL ``DecodeAny (Word (Encode (Branch (BGEU (31w,31w,-1w))))) = Branch (BGEU (31w,31w,-1w))``;
val _ = if aconv (rhs (concl bgeu_all_ones)) T then () else raise Fail "bgeu_all_ones";
val _ = (print "bgeu_all_ones="; print_term (rhs (concl bgeu_all_ones)); print "\n");
val bgeu_alias_sign = EVAL ``DecodeAny (Word (Encode (Branch (BGEU (1w,1w,0x800w))))) = Branch (BGEU (1w,1w,0x800w))``;
val _ = if aconv (rhs (concl bgeu_alias_sign)) T then () else raise Fail "bgeu_alias_sign";
val _ = (print "bgeu_alias_sign="; print_term (rhs (concl bgeu_alias_sign)); print "\n");
val bgeu_mixed = EVAL ``DecodeAny (Word (Encode (Branch (BGEU (7w,16w,0x57Fw))))) = Branch (BGEU (7w,16w,0x57Fw))``;
val _ = if aconv (rhs (concl bgeu_mixed)) T then () else raise Fail "bgeu_mixed";
val _ = (print "bgeu_mixed="; print_term (rhs (concl bgeu_mixed)); print "\n");
val bgeu_term = ``Encode (Branch (BGEU (rs1v,rs2v,immv)))``;
val bgeu_source = SIMP_CONV (srw_ss()) [Encode_def] bgeu_term;
val _ = (print "bgeu_source_clause="; print_term (concl bgeu_source); print "\n");
val _ = print ("bgeu_carrier_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (free_vars bgeu_term)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
