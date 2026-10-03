load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val update = GEN_ALL(prove(``state_rel ac k f f' s t lens extra ∧ v ≠ Handler ⇒
   state_rel ac k f f' (set_store v x s) (set_store v x t) lens extra``,
  simp[state_rel_def]
  \\ strip_tac
  \\ fs[wordSemTheory.set_store_def,stackSemTheory.set_store_def]
  \\ simp[FLOOKUP_UPDATE]
  \\ conj_tac
  >- (
    simp[fmap_eq_flookup]
    \\ simp[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM]
    \\ rw[] )
  \\ metis_tac[]));
val _ = theoremRow "store_update_full" update;
val _ = print("store_update_hypotheses=" ^ Int.toString(length(hyp update)) ^ "\n");
val _ = print("store_update_proved=" ^ term_to_string(rhs(concl(EQT_INTRO update))) ^ "\n");
