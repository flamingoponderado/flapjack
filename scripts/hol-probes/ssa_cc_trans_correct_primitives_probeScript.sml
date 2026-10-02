load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val exists_tac = qexists_tac`cst.permute`>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def
      ,ssa_cc_trans_def];
val skip_statement = Q.SPEC `Skip` ssa_cc_trans_correct;
val skip_case = prove (concl skip_statement, rpt strip_tac >>
    exists_tac);
val tick_statement = Q.SPEC `Tick` ssa_cc_trans_correct;
val tick_case = prove (concl tick_statement, rpt strip_tac >>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "sp_skip_full" skip_case;
val _ = out "sp_tick_full" tick_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "sp_type_st" "st" tick_case;
val _ = ty "sp_type_cst" "cst" tick_case;
val _ = ty "sp_type_ssa" "ssa" tick_case;
val _ = ty "sp_type_na" "na" tick_case;
val _ = ty "sp_type_lt" "lt" tick_case;
