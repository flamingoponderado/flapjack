load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "rawcall_full_statement="; print_term(concl comp_correct));
val _ = print("rawcall_full_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
val _ = (print "rawcall_case_statement="; print_term(concl(ISPEC ``stackLang$RawCall dest:64 stackLang$prog`` comp_correct)));

(* Original evaluate_ind has already been rewritten by fix_clock_evaluate
at stackSemScript1111. Its body post-state therefore matches the actual run. *)
val (_, induction_body) = strip_forall (concl stackSemTheory.evaluate_ind);
val (obligations, _) = dest_imp induction_body;
fun is_rawcall_obligation tm =
  let val (_, body) = strip_forall tm;
      val (_, conclusion) = strip_imp body;
      val (_, args) = strip_comb conclusion;
      val (program, _) = pairSyntax.dest_pair (hd args);
      val (constructor, _) = strip_comb program;
      val {Thy,Name,...} = dest_thy_const constructor
  in Thy = "stackLang" andalso Name = "RawCall" end
  handle HOL_ERR _ => false;
val rawcall_obligations = List.filter is_rawcall_obligation (strip_conj obligations);
val _ = if length rawcall_obligations = 1 then () else raise Fail "expected one original RawCall induction obligation";
val _ = if null(hyp stackSemTheory.evaluate_ind) then () else raise Fail "open induction theorem";
val _ = (print "rawcall_evaluate_ind_obligation="; print_term(hd rawcall_obligations));
