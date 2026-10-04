val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "blastLib"; load "preamble"; load "riscv_stepTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_stepTheory;
val defs = [Encode_def,UJtype_def,Itype_def,opc_def,Decode_def,boolify32_def,
            DecodeAny_def,asImm20_def];
val _ = computeLib.add_funs defs;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
(* Generic original kernel proofs over all intrinsic operands. *)
val jal_decode = Q.prove(
  `!rd imm. DecodeAny (Word (Encode (Branch (JAL (rd,imm))))) = Branch (JAL (rd,imm))`,
  rpt gen_tac >> simp defs >>
  CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >> simp [LET_THM] >> blastLib.BBLAST_TAC);
val jalr_decode = Q.prove(
  `!rd rs imm. DecodeAny (Word (Encode (Branch (JALR (rd,rs,imm))))) = Branch (JALR (rd,rs,imm))`,
  rpt gen_tac >> simp defs >>
  CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >> simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "jal_decode_universal="; print_term (concl jal_decode); print "\n");
val _ = print ("jal_decode_hypotheses=" ^ Int.toString (length (hyp jal_decode)) ^ "\n");
val _ = (print "jalr_decode_universal="; print_term (concl jalr_decode); print "\n");
val _ = print ("jalr_decode_hypotheses=" ^ Int.toString (length (hyp jalr_decode)) ^ "\n");
fun observation label q =
  let val th = EVAL q in
    if aconv (rhs (concl th)) T then () else raise Fail label;
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observation "jal_zero"
  ``DecodeAny (Word (Encode (Branch (JAL (0w,0w))))) = Branch (JAL (0w,0w))``;
val _ = observation "jal_all_ones"
  ``DecodeAny (Word (Encode (Branch (JAL (31w,-1w))))) = Branch (JAL (31w,-1w))``;
val _ = observation "jal_link_sign"
  ``DecodeAny (Word (Encode (Branch (JAL (1w,0x80000w))))) = Branch (JAL (1w,0x80000w))``;
val _ = observation "jal_scattered_bits"
  ``DecodeAny (Word (Encode (Branch (JAL (16w,0x5A53Fw))))) = Branch (JAL (16w,0x5A53Fw))``;
val _ = observation "jalr_zero"
  ``DecodeAny (Word (Encode (Branch (JALR (0w,0w,0w))))) = Branch (JALR (0w,0w,0w))``;
val _ = observation "jalr_all_ones"
  ``DecodeAny (Word (Encode (Branch (JALR (31w,31w,-1w))))) = Branch (JALR (31w,31w,-1w))``;
val _ = observation "jalr_link_alias"
  ``DecodeAny (Word (Encode (Branch (JALR (1w,1w,0x800w))))) = Branch (JALR (1w,1w,0x800w))``;
val _ = observation "jalr_mixed"
  ``DecodeAny (Word (Encode (Branch (JALR (7w,16w,0x57Fw))))) = Branch (JALR (7w,16w,0x57Fw))``;
val jal_term = ``Encode (Branch (JAL (rdv,immv)))``;
val jal_source = SIMP_CONV (srw_ss()) [Encode_def] jal_term;
val _ = (print "jal_source_clause="; print_term (concl jal_source); print "\n");
val _ = print ("jal_carrier_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (free_vars jal_term)) ^ "\n");
val jalr_term = ``Encode (Branch (JALR (rdv,rsv,immv)))``;
val jalr_source = SIMP_CONV (srw_ss()) [Encode_def] jalr_term;
val _ = (print "jalr_source_clause="; print_term (concl jalr_source); print "\n");
val _ = print ("jalr_carrier_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (free_vars jalr_term)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
