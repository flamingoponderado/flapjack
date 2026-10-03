val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
fun check source q =
  let val th = prove(q, METIS_TAC [source])
  in if null(hyp source) andalso null(hyp th) andalso aconv (concl th) q then th
     else raise Fail "original decoder transport theorem shape or hypotheses changed"
  end;
fun binders label th =
  let val (vars,_) = strip_forall (concl th)
  in print(label ^ "=");
     List.app (fn v => (print(fst(dest_var v) ^ ":"); print_type(type_of v); print ";")) vars;
     print "\n"
  end;
fun statement label th = (print(label ^ "="); print_term(concl th); print "\n");
val decodeWord = check riscv_stepTheory.Decode_IMP_DecodeAny
  ``!w i. riscv$Decode w = i ==> riscv_step$DecodeAny (riscv$Word w) = i``;
val _ = binders "decodeWord_binders" decodeWord;
val _ = statement "decodeWord_statement" decodeWord;
val _ = print "decodeWord_hypotheses=0\n";
val _ = print "decodeWord_proof=T\n";
val decodeHalf = check riscv_stepTheory.DecodeRVC_IMP_DecodeAny
  ``!h i. riscv$DecodeRVC h = i ==> riscv_step$DecodeAny (riscv$Half h) = i``;
val _ = binders "decodeHalf_binders" decodeHalf;
val _ = statement "decodeHalf_statement" decodeHalf;
val _ = print "decodeHalf_hypotheses=0\n";
val _ = print "decodeHalf_proof=T\n";
