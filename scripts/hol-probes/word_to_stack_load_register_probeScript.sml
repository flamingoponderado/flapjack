load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val registerLoad = prove(``wReg1 r (k,f,f') = (x ,r') ∧
  EVEN r ∧
  get_var r (s:('a,num # 'c,'ffi)state) = SOME c ∧
  state_rel ac k f f' s t lens 0 ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  state_rel ac k f f' s t' lens 0 ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
  t'.bitmaps = t.bitmaps /\
   (∀r. r ≠ k ⇒ get_var r t' = get_var r t) ∧
  r' ≠ k+1 ∧
  get_var r' t' = SOME c``,
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackLoad_def,stackSemTheory.evaluate_def,LET_THM,stackSemTheory.get_var_def]>>simp[]
    >-
    (drule_all state_rel_get_var_imp>>simp[]) >>
  IF_CASES_TAC>-fs[state_rel_def]>>
  reverse IF_CASES_TAC>-
    (fs[state_rel_def,LET_THM,get_var_def]>>
    res_tac>>fs[TWOxDIV2]>>rfs[]>>
    Cases_on`f'`>>fs[])>>
  imp_res_tac state_rel_get_var_imp2>>
  fs[]>>
  simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
  fs[TWOxDIV2]);
val _ = theoremRow "wload_full_register_transport" registerLoad;
val _ = theoremRow "wload_full_continuation" evaluate_wStackLoad_seq;
val _ = theoremRow "wload_original_definition" wStackLoad_def;
val _ = theoremRow "wload_original_register_compiler" wReg1_def;
