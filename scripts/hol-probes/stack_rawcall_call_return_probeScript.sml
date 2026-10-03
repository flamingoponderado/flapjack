load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
fun row label theorem = (print(label ^ "="); print_term(concl theorem));
val _ = row "call_return_full_statement" comp_correct;
val _ = print("call_return_full_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
val _ = row "call_return_case64" (ISPEC ``stackLang$Call (SOME (returnProg,5,7,9)) returnDest returnHandler:64 stackLang$prog`` comp_correct);
val _ = row "call_return_case80" (ISPEC ``stackLang$Call (SOME (returnProg,5,7,9)) returnDest returnHandler:80 stackLang$prog`` comp_correct);
val (_, induction_body) = strip_forall (concl stackSemTheory.evaluate_ind);
val (obligations, _) = dest_imp induction_body;
fun is_call_obligation tm =
  let val (_, body) = strip_forall tm;
      val (_, conclusion) = strip_imp body;
      val (_, args) = strip_comb conclusion;
      val (program, _) = pairSyntax.dest_pair (hd args);
      val (constructor, _) = strip_comb program;
      val {Thy,Name,...} = dest_thy_const constructor
  in Thy = "stackLang" andalso Name = "Call" end
  handle HOL_ERR _ => false;
val call_obligations = List.filter is_call_obligation (strip_conj obligations);
val _ = if length call_obligations = 1 andalso null(hyp stackSemTheory.evaluate_ind)
  then () else raise Fail "expected one closed original Call induction obligation";
val _ = (print "call_return_evaluate_ind_obligation="; print_term(hd call_obligations));
val _ = row "call_return_whole_case64" (ISPEC ``stackLang$Call returnOption returnDest returnHandler:64 stackLang$prog`` comp_correct);
val _ = row "call_return_direct64" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Call (SOME (Seq (StackFree 4) (Call NONE (INL 3) NONE),5,7,9)) (INL 3) NONE:64 stackLang$prog) = Call (SOME (RawCall 3,5,7,9)) (INL 3) NONE``);
val _ = row "call_return_handler64" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Call (SOME (Seq (StackFree 4) (Call NONE (INL 3) NONE),5,7,9)) (INR 6) (SOME (Seq (StackFree 6) (Call NONE (INL 3) NONE),11,13)):64 stackLang$prog) = Call (SOME (RawCall 3,5,7,9)) (INR 6) (SOME (Seq (StackFree 2) (RawCall 3),11,13))``);
val _ = row "call_return_link_erased64" (EVAL ``stackSem$find_code (INR 5) (((FEMPTY |+ (5,Loc 3 0)):num |-> 64 wordLang$word_loc) \\ 5) (insert 3 (Skip:64 stackLang$prog) LN) = NONE``);
val _ = row "call_return_other_link64" (EVAL ``stackSem$find_code (INR 6) (((FEMPTY |+ (6,Loc 3 0)):num |-> 64 wordLang$word_loc) \\ 5) (insert 3 (Skip:64 stackLang$prog) LN) = SOME Skip``);
val _ = row "call_return_whole_case80" (ISPEC ``stackLang$Call returnOption returnDest returnHandler:80 stackLang$prog`` comp_correct);
val _ = row "call_return_direct80" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Call (SOME (Seq (StackFree 4) (Call NONE (INL 3) NONE),5,7,9)) (INL 3) NONE:80 stackLang$prog) = Call (SOME (RawCall 3,5,7,9)) (INL 3) NONE``);
val _ = row "call_return_handler80" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Call (SOME (Seq (StackFree 4) (Call NONE (INL 3) NONE),5,7,9)) (INR 6) (SOME (Seq (StackFree 6) (Call NONE (INL 3) NONE),11,13)):80 stackLang$prog) = Call (SOME (RawCall 3,5,7,9)) (INR 6) (SOME (Seq (StackFree 2) (RawCall 3),11,13))``);
val _ = row "call_return_link_erased80" (EVAL ``stackSem$find_code (INR 5) (((FEMPTY |+ (5,Loc 3 0)):num |-> 80 wordLang$word_loc) \\ 5) (insert 3 (Skip:80 stackLang$prog) LN) = NONE``);
val _ = row "call_return_other_link80" (EVAL ``stackSem$find_code (INR 6) (((FEMPTY |+ (6,Loc 3 0)):num |-> 80 wordLang$word_loc) \\ 5) (insert 3 (Skip:80 stackLang$prog) LN) = SOME Skip``);
