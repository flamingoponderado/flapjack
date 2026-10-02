load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Original full scoped injection theorem; source6405-6423 manually compared. *)
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "rename_move_distinct_full" list_next_var_rename_move_distinct;
val _ = ty "rename_move_distinct_type_input" "ssa" list_next_var_rename_move_distinct;
val _ = ty "rename_move_distinct_type_output" "ssa'" list_next_var_rename_move_distinct;
val _ = ty "rename_move_distinct_type_names" "ls" list_next_var_rename_move_distinct;
val _ = ty "rename_move_distinct_type_move" "mov" list_next_var_rename_move_distinct;
val _ = ty "rename_move_distinct_type_next" "na" list_next_var_rename_move_distinct;
val _ = ty "rename_move_distinct_type_key" "x" list_next_var_rename_move_distinct;
