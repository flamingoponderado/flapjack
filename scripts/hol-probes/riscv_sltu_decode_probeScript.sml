val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "blastLib"; load "preamble"; load "riscv_stepTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_stepTheory;
val _ = computeLib.add_funs [Encode_def,Rtype_def,opc_def,Decode_def,boolify32_def,DecodeAny_def];
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
(* Generic kernel proof using the original native definitions, not a fixture. *)
val sltu_decode = Q.prove(
  `!rd rs1 rs2. DecodeAny (Word (Encode (ArithR (SLTU (rd,rs1,rs2))))) = ArithR (SLTU (rd,rs1,rs2))`,
  rpt gen_tac >> simp [DecodeAny_def, Encode_def, Rtype_def, opc_def, Decode_def, boolify32_def] >>
  CONV_TAC (DEPTH_CONV blastLib.BBLAST_CONV) >> simp [LET_THM] >> blastLib.BBLAST_TAC);
val _ = (print "sltu_decode_universal="; print_term(concl sltu_decode); print "\n");
val _ = print ("sltu_decode_hypotheses=" ^ Int.toString(length(hyp sltu_decode)) ^ "\n");
val sltu_decode_zero = EVAL ``DecodeAny (Word (Encode (ArithR (SLTU (0w,0w,0w))))) = ArithR (SLTU (0w,0w,0w))``;
val _ = if aconv (rhs(concl sltu_decode_zero)) T then () else raise Fail "sltu_decode_zero";
val _ = (print "sltu_decode_zero="; print_term(rhs(concl sltu_decode_zero)); print "\n");
val sltu_decode_all_ones = EVAL ``DecodeAny (Word (Encode (ArithR (SLTU (31w,31w,31w))))) = ArithR (SLTU (31w,31w,31w))``;
val _ = if aconv (rhs(concl sltu_decode_all_ones)) T then () else raise Fail "sltu_decode_all_ones";
val _ = (print "sltu_decode_all_ones="; print_term(rhs(concl sltu_decode_all_ones)); print "\n");
val sltu_decode_high_bit = EVAL ``DecodeAny (Word (Encode (ArithR (SLTU (1w,0w,16w))))) = ArithR (SLTU (1w,0w,16w))``;
val _ = if aconv (rhs(concl sltu_decode_high_bit)) T then () else raise Fail "sltu_decode_high_bit";
val _ = (print "sltu_decode_high_bit="; print_term(rhs(concl sltu_decode_high_bit)); print "\n");
val sltu_decode_alias = EVAL ``DecodeAny (Word (Encode (ArithR (SLTU (7w,7w,7w))))) = ArithR (SLTU (7w,7w,7w))``;
val _ = if aconv (rhs(concl sltu_decode_alias)) T then () else raise Fail "sltu_decode_alias";
val _ = (print "sltu_decode_alias="; print_term(rhs(concl sltu_decode_alias)); print "\n");
val sltu_term = ``Encode (ArithR (SLTU (rdv,rs1v,rs2v)))``;
val sltu_source = SIMP_CONV (srw_ss()) [Encode_def] sltu_term;
val _ = (print "sltu_encode_source_clause="; print_term(concl sltu_source); print "\n");
val _ = print ("sltu_carrier_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars sltu_term)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
