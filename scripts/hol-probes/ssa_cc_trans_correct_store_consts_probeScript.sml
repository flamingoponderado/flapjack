load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Original kernel specialization; original StoreConsts9608-9647 manually compared. *)
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val store_case = Q.SPEC `wordLang$StoreConsts (n:num) (n0:num) (n1:num) (n2:num) (l:(bool # 'a word) list)` ssa_cc_trans_correct;
val _ = out "store_consts_full" store_case;
val _ = ty "store_consts_type_tmp" "n" store_case;
val _ = ty "store_consts_type_address" "n1" store_case;
val _ = ty "store_consts_type_offset" "n2" store_case;
val _ = ty "store_consts_type_words" "l" store_case;
val _ = ty "store_consts_type_st" "st" store_case;
val _ = ty "store_consts_type_cst" "cst" store_case;
val _ = ty "store_consts_type_ssa" "ssa" store_case;
val _ = ty "store_consts_type_next" "na" store_case;
val _ = ty "store_consts_type_tables" "lt" store_case;
