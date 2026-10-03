load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val evaluate_wStackLoad_clock = prove(``∀x t.
 evaluate(wStackLoad x Skip,t with clock:= clk) =
 (I ## (\s. s with clock := clk)) (evaluate(wStackLoad x Skip,t))``,
 Induct>>fs[wStackLoad_def,FORALL_PROD,stackSemTheory.evaluate_def,LET_THM]>>rw[]);
val transport = prove(``state_rel ac k f f' s t lens extra ⇒
 ∃t':('a,'c,'ffi) stackSem$state.
 evaluate(const_inst (k+1) i,t) = (NONE,t') ∧
 t.clock = t'.clock ∧ state_rel ac k f f' s t' lens extra ∧
 LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
 get_var (k+1) t' = SOME (Word i)``,
 simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock] >>
 simp[stackSemTheory.inst_def] >> simp[stackSemTheory.assign_def] >>
 simp[stackSemTheory.word_exp_def]);
val clockLaw = prove(``evaluate(const_inst k i,t with clock:=clk) =
 (I ## (\t. t with clock:=clk)) (evaluate(const_inst k i,t))``,
 fs[stackSemTheory.evaluate_def] >> Cases_on `inst (Const k i) t` >> fs[]);
val _ = theoremRow "const_full_transport" transport;
val _ = theoremRow "const_full_clock" clockLaw;
val _ = theoremRow "const_transport_closed" (EQT_INTRO transport);
val _ = theoremRow "const_clock_closed" (EQT_INTRO clockLaw);
