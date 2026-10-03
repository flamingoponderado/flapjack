load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val write = GEN_ALL(prove(``state_rel ac k f f' s t lens 0 ∧
   m < f' + k ∧
   (∀n.  n ≤ k ⇒
     evaluate (kont n, t) = (NONE, set_var n v t))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' (set_var (2 * m) v s) t' lens 0 /\
   LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space``,
  rw[wRegWrite1_def,LET_THM,TWOxDIV2]
  >- ( metis_tac[ state_rel_set_var, LESS_OR_EQ] )
  \\ rw[stackSemTheory.evaluate_def]
  >- fs[state_rel_def]
  >-
    (fs[state_rel_def]>>
    Cases_on`f'`>>fs[])
  \\ simp[]
  \\ match_mp_tac state_rel_set_var2
  \\ simp[]));
val _ = theoremRow "register_write_full" write;
val _ = print("register_write_hypotheses=" ^ Int.toString(length(hyp write)) ^ "\n");
val _ = print("register_write_proved=" ^ term_to_string(rhs(concl(EQT_INTRO write))) ^ "\n");
