load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory wordSemTheory wordLangTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
(* Local original lemmas are replayed with their literal source statements and
   proof scripts, without saving anything into the reference development. *)
val collapse = Q.prove (`evaluate (P,s) = (NONE,t) ==> evaluate (Seq P Q,s) = evaluate (Q,t)`, simp[evaluate_def]);
val empty_cut = Q.prove (`cut_env (a,fromAList (MAP (g:num#unit -> num#unit) (toAList LN))) v = cut_env (a,LN) v`,
  simp[cut_env_def,cut_envs_def,cut_names_def,sptreeTheory.toAList_def,sptreeTheory.foldi_def,sptreeTheory.fromAList_def] >> rpt CASE_TAC >> simp[]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "collapse_full" collapse;
val _ = out "empty_cut_full" empty_cut;
val _ = ty "collapse_type_first" "P" collapse;
val _ = ty "collapse_type_source" "s" collapse;
val _ = ty "collapse_type_after" "t" collapse;
val _ = ty "empty_cut_type_names" "a" empty_cut;
val _ = ty "empty_cut_type_locals" "v" empty_cut;
val _ = ty "empty_cut_type_map" "g" empty_cut;
