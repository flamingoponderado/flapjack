load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory stackLangTheory;
val _ = Globals.linewidth := 1000000;
val statement = ``raise_stub F k =
    Seq (Get k Handler)
   (Seq (StackSetSize k)
   (Seq Skip
   (Seq (StackLoad k 2)
   (Seq (Set Handler k)
   (Seq (StackLoad k 1)
   (Seq (StackFree 3)
        (Raise k)))))))``;
val replay = GEN_ALL(prove(statement, simp [raise_stub_def, handler_slots_def]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open Raise stub theorem";
val _ = (print "raise_stub_false_statement="; print_term(concl replay); print "\n");
val _ = print("raise_stub_false_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("raise_stub_false_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
