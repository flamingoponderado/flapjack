load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val cut = GEN_ALL(prove(``  state_rel ac k f f' s t lens 0 ∧
  cut_state (names, LN) s = SOME s' ⇒
  state_rel ac k f f' s' t lens 0``,
  rw[wordSemTheory.cut_state_def, AllCaseEqs()] \\
  fs[state_rel_def] \\
  fs[wordSemTheory.cut_env_def, wordSemTheory.cut_envs_def,
     wordSemTheory.cut_names_def, AllCaseEqs()] \\
  rveq \\
  rpt conj_tac
  >- metis_tac[]
  >- (simp[wf_union, wf_inter])
  \\ rpt gen_tac \\ strip_tac
  \\ fs[lookup_union, lookup_inter, AllCaseEqs(), lookup_def]));
val _ = theoremRow "cut_state_full" cut;
val _ = print("cut_state_hypotheses=" ^ Int.toString(length(hyp cut)) ^ "\n");
val _ = print("cut_state_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cut))) ^ "\n");
