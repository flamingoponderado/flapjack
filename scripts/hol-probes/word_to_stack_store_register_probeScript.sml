load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val store_reg1 = GEN_ALL(prove(``  wReg1 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  state_rel ac k f f' (s:('a,num # 'c,'ffi) wordSem$state) (t:('a,'c,'ffi) stackSem$state) lens 0 ∧
  LENGTH t.stack = LENGTH_t_stack ∧
  t.stack_space = t_stack_space
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackStore x Skip,(set_var r' c t)) = (NONE,t') ∧
  state_rel ac k f f' (set_var r c s) t' lens 0 ∧
  LENGTH t'.stack = LENGTH_t_stack /\ t'.stack_space = t_stack_space``,
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackStore_def,stackSemTheory.evaluate_def,LET_THM,stackSemTheory.get_var_def]>>simp[]>-
   (irule state_rel_set_var >> fs[]) >>
  IF_CASES_TAC >- fs[state_rel_def] >>
  IF_CASES_TAC >- (fs[state_rel_def] >>
     Cases_on `f' = 0` >> fs[])>>
  fs[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE] >>
  irule state_rel_set_var2 >> fs[]));
val _ = theoremRow "store_reg1_full" store_reg1;
val _ = print("store_reg1_hypotheses=" ^ Int.toString(length(hyp store_reg1)) ^ "\n");
val _ = print("store_reg1_proved=" ^ term_to_string(rhs(concl(EQT_INTRO store_reg1))) ^ "\n");

val write_seq = GEN_ALL(prove(``  evaluate (wRegWrite1 g r (k,f,f'),t) =
  (let (l,n) = wReg1 r (k,f,f') in
  evaluate ((Seq (g n) (wStackStore l Skip)),t))``,
  rw[] >> pairarg_tac >> fs[] >>
  simp[stackSemTheory.evaluate_def,wRegWrite1_def] >>
  IF_CASES_TAC >> gvs[wStackStore_def,wReg1_def]
  >-(pairarg_tac >> simp[] >>
    IF_CASES_TAC >> simp[stackSemTheory.evaluate_def])
  >-(
   pairarg_tac >> simp[] >>
   simp[el 10 $ CONJUNCTS stackSemTheory.evaluate_def] >>
   simp[el 1 $ CONJUNCTS stackSemTheory.evaluate_def])));
val _ = theoremRow "write_seq_full" write_seq;
val _ = print("write_seq_hypotheses=" ^ Int.toString(length(hyp write_seq)) ^ "\n");
val _ = print("write_seq_proved=" ^ term_to_string(rhs(concl(EQT_INTRO write_seq))) ^ "\n");
