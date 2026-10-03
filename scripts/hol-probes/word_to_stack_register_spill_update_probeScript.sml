load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val update = GEN_ALL(prove(``state_rel ac k f f' s t lens 0 ∧
  ¬(x < k) ∧ x < f' + k ∧ st = t.stack ∧ sp = t.stack_space ⇒
  state_rel ac k f f' (set_var (2*x) v s)
    (t with stack := LUPDATE v (sp + (f + k − (x + 1))) st) lens 0``,
  simp[state_rel_def,stackSemTheory.set_var_def,wordSemTheory.set_var_def,stack_size_rel_def]
  \\ strip_tac \\ rveq
  \\ fs[lookup_insert,FLOOKUP_UPDATE,wf_insert]
  \\ CONJ_TAC THEN1 metis_tac[]
  \\ `0<f` by
      (Cases_on`f'`>>fs[]>>DECIDE_TAC)
  \\ simp[DROP_LUPDATE]
  \\ CONJ_TAC >-  gvs[stack_rel_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp[]
  >- (
    strip_tac \\ rveq \\
    simp[EVEN_MULT]
    \\ ONCE_REWRITE_TAC[MULT_COMM]
    \\ simp[MULT_DIV]
    \\ simp[LLOOKUP_THM]
    \\ simp[EL_LUPDATE])
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ IF_CASES_TAC >> fs[]
  \\ imp_res_tac LLOOKUP_TAKE_IMP
  \\ fs[LLOOKUP_DROP,LLOOKUP_LUPDATE]
  \\ fs[EVEN_EXISTS]
  \\ rfs[]));
val _ = theoremRow "register_spill_update_full" update;
val _ = print("register_spill_update_hypotheses=" ^ Int.toString(length(hyp update)) ^ "\n");
val _ = print("register_spill_update_proved=" ^ term_to_string(rhs(concl(EQT_INTRO update))) ^ "\n");
