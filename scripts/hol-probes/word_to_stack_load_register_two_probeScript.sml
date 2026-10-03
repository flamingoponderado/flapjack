load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val registerLoad = GEN_ALL(prove(``
  wReg2 r (k,f,f') = (x ,r') ∧
  EVEN r ∧
  get_var r (s:('a,num # 'c,'ffi)state) = SOME c ∧
  state_rel ac k f f' s t lens 0 ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  t.bitmaps = t'.bitmaps /\
  state_rel ac k f f' s t' lens 0 ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
  (∀r. r ≠ k+1 ⇒ get_var r t' = get_var r t) ∧
  (∀r c. r ≠ k + 1 ⇒
  word_exp t' (Op Add [Var r;Const c]) = word_exp t (Op Add [Var r; Const c])) /\
  get_var r' t' = SOME c``,
  rw[wReg2_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackLoad_def,stackSemTheory.evaluate_def,LET_THM,
  stackSemTheory.get_var_def,stackSemTheory.word_exp_def]>>simp[]>-
    (
    imp_res_tac state_rel_get_var_imp>>
    first_assum match_mp_tac>>
    simp[TWOxDIV2])>>

  IF_CASES_TAC>-fs[state_rel_def]>>
  reverse IF_CASES_TAC>-
    (fs[state_rel_def,LET_THM,get_var_def]>>
    res_tac>>fs[TWOxDIV2]>>rfs[]>>
    Cases_on`f'`>>fs[])>>
  imp_res_tac state_rel_get_var_imp2>>
  fs[]>>
  simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE]));
val _ = theoremRow "wload2_full_register_transport" registerLoad;
val _ = print("wload2_full_hypotheses=" ^ Int.toString(length(hyp registerLoad)) ^ "\n");
val _ = print("wload2_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO registerLoad))) ^ "\n");
val _ = theoremRow "wload2_original_register_compiler" wReg2_def;
