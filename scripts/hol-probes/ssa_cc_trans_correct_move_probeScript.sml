load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Original kernel specialization; original Move proof7740-7858 compared manually. *)
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val move_case = Q.SPEC `wordLang$Move (pri:num) (ls:(num # num) list)` ssa_cc_trans_correct;
val _ = out "move_full" move_case;
val _ = ty "move_type_priority" "pri" move_case;
val _ = ty "move_type_moves" "ls" move_case;
val _ = ty "move_type_st" "st" move_case;
val _ = ty "move_type_cst" "cst" move_case;
val _ = ty "move_type_ssa" "ssa" move_case;
val _ = ty "move_type_next" "na" move_case;
val _ = ty "move_type_tables" "lt" move_case;
