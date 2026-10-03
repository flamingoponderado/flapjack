load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory asmPropsTheory asmTheory;
val local_nonempty = prove (``enc_ok c /\ asm_ok w c ==> (c.encode w <> [])``,
  METIS_TAC [listTheory.LENGTH_NIL,enc_ok_def]);
val _ = if null(hyp local_nonempty) then
 (print "encoding_nonempty_statement="; print_term(concl local_nonempty); print "\n")
 else raise Fail "local hypotheses";
val _ = OS.Process.exit OS.Process.success;
