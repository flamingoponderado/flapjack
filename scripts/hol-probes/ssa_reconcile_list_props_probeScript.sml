load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val ssa_reconcile_moves_eq = prove (``∀L.
    FILTER (λ(a,b). a ≠ b)
      (FLAT (MAP (λv. case lookup v m of
                      | NONE => []
                      | SOME cv => [(f v, cv)]) L)) =
    MAP (λv. (f v, THE (lookup v m)))
      (FILTER (λv. case lookup v m of NONE => F | SOME cv => f v ≠ cv) L)``,
Induct >> simp[] >>
  strip_tac >>
  Cases_on `lookup h m` >> fs[] >>
  IF_CASES_TAC >> simp[]);
val ssa_reconcile_filtered_all_distinct = prove (``ALL_DISTINCT (FILTER (λv. case lookup v cur_ssa of
                            | NONE => F
                            | SOME cv => option_lookup tgt_ssa v ≠ cv)
                  (MAP FST (toAList ns)))``,
match_mp_tac FILTER_ALL_DISTINCT >>
  simp[ALL_DISTINCT_MAP_FST_toAList]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "sr_moves_full" ssa_reconcile_moves_eq;
val _ = out "sr_filtered_full" ssa_reconcile_filtered_all_distinct;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(fst(strip_forall(concl th)) @ free_vars(concl th))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "sr_type_L" "L" ssa_reconcile_moves_eq;
val _ = ty "sr_type_m" "m" ssa_reconcile_moves_eq;
val _ = ty "sr_type_f" "f" ssa_reconcile_moves_eq;
val _ = ty "sr_type_cur_ssa" "cur_ssa" ssa_reconcile_filtered_all_distinct;
val _ = ty "sr_type_tgt_ssa" "tgt_ssa" ssa_reconcile_filtered_all_distinct;
val _ = ty "sr_type_ns" "ns" ssa_reconcile_filtered_all_distinct;
