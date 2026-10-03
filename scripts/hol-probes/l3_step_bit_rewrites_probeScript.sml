val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
fun check source q =
  let val th = prove(q, METIS_TAC [source])
  in if null(hyp source) andalso null(hyp th) andalso aconv (concl th) q then th
     else raise Fail "original step bit rewrite theorem shape or hypotheses changed"
  end;
fun binders label th =
  let val (vars,_) = strip_forall (concl th)
  in print(label ^ "=");
     List.app (fn v => (print(fst(dest_var v) ^ ":"); print_type(type_of v); print ";")) vars;
     print "\n"
  end;
fun statement label th = (print(label ^ "="); print_term(concl th); print "\n");
val bit10 = check riscv_stepTheory.word_bit_1_0
  ``!x0 x1 x2 x3 x4 x5 x6 x7.
 (word_bit 1 (v2w [x0;x1;x2;x3;x4;x5;x6;x7]:word8) = x6) /\
 (word_bit 0 (v2w [x0;x1;x2;x3;x4;x5;x6;x7]:word8) = x7)``;
val _ = binders "bit10_binders" bit10;
val _ = statement "bit10_statement" bit10;
val _ = print "bit10_hypotheses=0\n";
val _ = print "bit10_proof=T\n";
val bit0 = check riscv_stepTheory.word_bit_0_lemmas
  ``!w v.
 ~word_bit 0 (0xFFFFFFFFFFFFFFFEw && w:word64) /\
 word_bit 0 ((0xFFFFFFFFFFFFFFFEw && w:word64) + v) = word_bit 0 v``;
val _ = binders "bit0_binders" bit0;
val _ = statement "bit0_statement" bit0;
val _ = print "bit0_hypotheses=0\n";
val _ = print "bit0_proof=T\n";
val v2w0 = check riscv_stepTheory.v2w_0_rwts
  ``!b3 b2 b1 b0.
 ((v2w [F;F;F;F;T] = 1w:word5)) /\
 ((v2w [F;F;F;F;F] = 0w:word5)) /\
 ((v2w [T;b3;b2;b1;b0] = 0w:word5) = F) /\
 ((v2w [b3;T;b2;b1;b0] = 0w:word5) = F) /\
 ((v2w [b3;b2;T;b1;b0] = 0w:word5) = F) /\
 ((v2w [b3;b2;b1;T;b0] = 0w:word5) = F) /\
 ((v2w [b3;b2;b1;b0;T] = 0w:word5) = F)``;
val _ = binders "v2w0_binders" v2w0;
val _ = statement "v2w0_statement" v2w0;
val _ = print "v2w0_hypotheses=0\n";
val _ = print "v2w0_proof=T\n";
val bitShift = check riscv_stepTheory.word_bit_add_lsl_simp
  ``!x w. word_bit 0 (x + w << 1) = word_bit 0 (x:word64)``;
val _ = binders "bitShift_binders" bitShift;
val _ = statement "bitShift_statement" bitShift;
val _ = print "bitShift_hypotheses=0\n";
val _ = print "bitShift_proof=T\n";
val _ = (print "v2w8_type="; print_type(type_of ``v2w : bool list -> word8``); print "\n");
val _ = (print "v2w5_type="; print_type(type_of ``v2w : bool list -> word5``); print "\n");
