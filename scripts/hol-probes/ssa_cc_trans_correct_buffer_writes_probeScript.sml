load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Original kernel specializations; original exp_tac2 and resumed buffer cases compared. *)
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val code_case = Q.SPEC `wordLang$CodeBufferWrite (r1:num) (r2:num)` ssa_cc_trans_correct;
val data_case = Q.SPEC `wordLang$DataBufferWrite (r1:num) (r2:num)` ssa_cc_trans_correct;
val _ = out "buffer_code_full" code_case;
val _ = out "buffer_data_full" data_case;
val _ = ty "buffer_type_first" "r1" code_case;
val _ = ty "buffer_type_second" "r2" code_case;
val _ = ty "buffer_type_st" "st" code_case;
val _ = ty "buffer_type_cst" "cst" code_case;
val _ = ty "buffer_type_ssa" "ssa" code_case;
val _ = ty "buffer_type_next" "na" code_case;
val _ = ty "buffer_type_tables" "lt" code_case;
