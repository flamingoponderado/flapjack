load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun caseRows name instruction = let
  val result = GEN_ALL (Q.SPEC instruction word_to_stackProofTheory.evaluate_wInst)
  val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open instruction case"
  val _ = (print (name ^ "_typed="); Lib.with_flag (Globals.show_types,true) print_term (concl result))
  val _ = print(name ^ "_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n")
  val _ = print(name ^ "_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n")
in () end;
val _ = caseRows "carry" `(asm$Arith (asm$AddCarry flag_destination flag_left flag_right flag_register) : 'a asm$inst)`;
val _ = caseRows "addOverflow" `(asm$Arith (asm$AddOverflow flag_destination flag_left flag_right flag_register) : 'a asm$inst)`;
val _ = caseRows "subOverflow" `(asm$Arith (asm$SubOverflow flag_destination flag_left flag_right flag_register) : 'a asm$inst)`;
