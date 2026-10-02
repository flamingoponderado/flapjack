load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "if_full_statement="; print_term(concl comp_correct));
val _ = print("if_full_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
val _ = (print "if_case_statement="; print_term(concl(ISPEC ``stackLang$If comparison register operand branchOne branchTwo:64 stackLang$prog`` comp_correct)));

(* Extract the actual guarded case obligation from the original induction
theorem. This is source IH-shape evidence, not an IH-free comp_correct instance. *)
val (_, induction_body) = strip_forall (concl stackSemTheory.evaluate_ind);
val (obligations, _) = dest_imp induction_body;
fun is_if_obligation tm =
  let val (_, body) = strip_forall tm;
      val (_, conclusion) = strip_imp body;
      val (_, args) = strip_comb conclusion;
      val (program, _) = pairSyntax.dest_pair (hd args);
      val (constructor, _) = strip_comb program;
      val {Thy,Name,...} = dest_thy_const constructor
  in Thy = "stackLang" andalso Name = "If" end
  handle HOL_ERR _ => false;
val if_obligations = List.filter is_if_obligation (strip_conj obligations);
val _ = if length if_obligations = 1 then () else raise Fail "expected one original If induction obligation";
val _ = if null(hyp stackSemTheory.evaluate_ind) then () else raise Fail "open induction theorem";
val _ = (print "if_evaluate_ind_obligation="; print_term(hd if_obligations));
