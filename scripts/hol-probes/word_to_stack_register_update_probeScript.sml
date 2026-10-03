load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val update = GEN_ALL(prove(``state_rel ac k f f' s t lens extra ∧
    x < k ⇒
    state_rel ac k f f' (set_var (2*x) v s) (set_var x v t) lens extra``,
  simp[state_rel_def,stackSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ strip_tac
  \\ fs[lookup_insert,FLOOKUP_UPDATE,wf_insert]
  \\ CONJ_TAC THEN1 metis_tac[]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp[]
  >- (
    simp[EVEN_MULT]
    \\ ONCE_REWRITE_TAC[MULT_COMM]
    \\ simp[MULT_DIV] )
  \\ strip_tac
  \\ Cases_on`x = n DIV 2` \\ simp[]
  \\ rveq
  \\ fs[bitTheory.DIV_MULT_THM2]
  \\ `EVEN n` by metis_tac[]
  \\ fs[EVEN_MOD2]));
val _ = theoremRow "register_update_full" update;
val _ = print("register_update_hypotheses=" ^ Int.toString(length(hyp update)) ^ "\n");
val _ = print("register_update_proved=" ^ term_to_string(rhs(concl(EQT_INTRO update))) ^ "\n");
