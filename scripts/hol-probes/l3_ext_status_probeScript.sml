load "riscvTheory"; load "wordsLib";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory;
val _ = Globals.linewidth := 100000;
val _ = (print "ext_status_definition=";print_term(concl ext_status_def);print "\n");
val _ = (print "ext_status_type=";print_type(type_of ``riscv$ext_status``);print "\n");
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = computeLib.add_funs [ext_status_def];
val _ = out "off" ``ext_status Off``;
val _ = out "initial" ``ext_status Initial``;
val _ = out "clean" ``ext_status Clean``;
val _ = out "dirty" ``ext_status Dirty``;
