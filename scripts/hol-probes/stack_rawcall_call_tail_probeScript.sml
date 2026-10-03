load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
fun row label theorem = (print(label ^ "="); print_term(concl theorem));
val _ = row "call_tail_full_statement" comp_correct;
val _ = print("call_tail_full_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
val _ = row "call_tail_case64" (ISPEC ``stackLang$Call NONE tailDest tailHandler:64 stackLang$prog`` comp_correct);
val _ = row "call_tail_case80" (ISPEC ``stackLang$Call NONE tailDest tailHandler:80 stackLang$prog`` comp_correct);
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
val _ = (print "call_tail_evaluate_ind_obligation="; print_term(hd call_obligations));
val _ = row "call_tail_direct64" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Call NONE (INL 3) NONE:64 stackLang$prog) = Call NONE (INL 3) NONE``);
val _ = row "call_tail_handler64" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Call NONE (INR 5) (SOME (Seq (StackFree 4) (Call NONE (INL 3) NONE),7,9)):64 stackLang$prog) = Call NONE (INR 5) (SOME (Seq (StackFree 4) (Call NONE (INL 3) NONE),7,9))``);
val _ = row "call_tail_direct80" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Call NONE (INL 3) NONE:80 stackLang$prog) = Call NONE (INL 3) NONE``);
val _ = row "call_tail_handler80" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Call NONE (INR 5) (SOME (Seq (StackFree 4) (Call NONE (INL 3) NONE),7,9)):80 stackLang$prog) = Call NONE (INR 5) (SOME (Seq (StackFree 4) (Call NONE (INL 3) NONE),7,9))``);
