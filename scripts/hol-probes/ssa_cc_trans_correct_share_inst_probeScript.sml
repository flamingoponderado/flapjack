load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Original kernel specialization; ShareInst10012-10045 manually compared. *)
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val share_case = Q.SPEC `wordLang$ShareInst (m:asm$memop) (n:num) (e:'a wordLang$exp)` ssa_cc_trans_correct;
val _ = out "share_inst_full" share_case;
val _ = ty "share_inst_type_operator" "m" share_case;
val _ = ty "share_inst_type_name" "n" share_case;
val _ = ty "share_inst_type_expression" "e" share_case;
val _ = ty "share_inst_type_st" "st" share_case;
val _ = ty "share_inst_type_cst" "cst" share_case;
val _ = ty "share_inst_type_ssa" "ssa" share_case;
val _ = ty "share_inst_type_next" "na" share_case;
val _ = ty "share_inst_type_tables" "lt" share_case;
