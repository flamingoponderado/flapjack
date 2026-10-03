load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory wordSemTheory
  stackSemTheory wordLangTheory stackLangTheory miscTheory sptreeTheory;
val _ = Globals.linewidth := 1000000;
val th = GEN_ALL compile_result_def;
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open definition";
val _ = (print "compile_result_definition="; print_term(concl th));
val _ = print("compile_result_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = (print "compile_result_type="; print_type(type_of(``compile_result``)); print "\n");
val th = GEN_ALL push_locals_def;
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open definition";
val _ = (print "push_locals_definition="; print_term(concl th));
val _ = print("push_locals_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = (print "push_locals_type="; print_type(type_of(``push_locals``)); print "\n");
val th = GEN_ALL(prove(``(Halt (Word 1w) = compile_result z <=> z = NotEnoughSpace) /\
    (good_dimindex (:'a) ==> Halt (Word (2w:'a word)) <> compile_result z)``,
  Cases_on `z` \\ fs [] \\ fs [good_dimindex_def] \\ rw [] \\ fs [dimword_def]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
val _ = (print "halt_eq_compile_result_statement="; print_term(concl th));
val _ = print("halt_eq_compile_result_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("halt_eq_compile_result_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
