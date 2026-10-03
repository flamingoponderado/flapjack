load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "seq_full_statement="; print_term(concl comp_correct));
val _ = print("seq_full_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
fun row label theorem = (print(label ^ "="); print_term(concl theorem));
val _ = row "seq_case64" (ISPEC ``stackLang$Seq seqLeftProg seqRightProg:64 stackLang$prog`` comp_correct);
val _ = row "seq_case80" (ISPEC ``stackLang$Seq seqLeftProg seqRightProg:80 stackLang$prog`` comp_correct);
val (_, induction_body) = strip_forall (concl stackSemTheory.evaluate_ind);
val (obligations, _) = dest_imp induction_body;
fun is_seq_obligation tm =
  let val (_, body) = strip_forall tm;
      val (_, conclusion) = strip_imp body;
      val (_, args) = strip_comb conclusion;
      val (program, _) = pairSyntax.dest_pair (hd args);
      val (constructor, _) = strip_comb program;
      val {Thy,Name,...} = dest_thy_const constructor
  in Thy = "stackLang" andalso Name = "Seq" end
  handle HOL_ERR _ => false;
val seq_obligations = List.filter is_seq_obligation (strip_conj obligations);
val _ = if length seq_obligations = 1 andalso null(hyp stackSemTheory.evaluate_ind)
  then () else raise Fail "expected one closed original Seq induction obligation";
val _ = (print "seq_evaluate_ind_obligation="; print_term(hd seq_obligations));
val _ = row "seq_equal64" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Seq (StackFree 4) (Call NONE (INL 3) NONE):64 stackLang$prog) = RawCall 3``);
val _ = row "seq_equal80" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Seq (StackFree 4) (Call NONE (INL 3) NONE):80 stackLang$prog) = RawCall 3``);
val _ = row "seq_less64" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Seq (StackFree 6) (Call NONE (INL 3) NONE):64 stackLang$prog) = Seq (StackFree 2) (RawCall 3)``);
val _ = row "seq_less80" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Seq (StackFree 6) (Call NONE (INL 3) NONE):80 stackLang$prog) = Seq (StackFree 2) (RawCall 3)``);
val _ = row "seq_greater64" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Seq (StackFree 2) (Call NONE (INL 3) NONE):64 stackLang$prog) = Seq Tick (Seq (StackAlloc 2) (RawCall 3))``);
val _ = row "seq_greater80" (EVAL ``stack_rawcall$comp (insert 3 4 LN) (Seq (StackFree 2) (Call NONE (INL 3) NONE):80 stackLang$prog) = Seq Tick (Seq (StackAlloc 2) (RawCall 3))``);
