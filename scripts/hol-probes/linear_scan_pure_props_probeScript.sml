(* Direct original linear_scan proposition-valued definitions; CakeML remains read-only.
   EVAL rows decide closed instances; the check_intervals rows are HOL proofs
   that hold without any fact about THE NONE. *)
load "bossLib";
load "preamble";
load "intLib";
load "linear_scanTheory";
open bossLib HolKernel Parse preamble linear_scanTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
fun print_simp label q =
  let val th = (SIMP_CONV (srw_ss()) [check_startlive_prop_def, live_tree_registers_def, size_of_live_tree_def] THENC EVAL THENC SIMP_CONV (srw_ss()) []) q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
fun print_prove label q tac =
  let val _ = prove (q, tac) in print (label ^ "=T\n") end;
val _ = print_eval "cnp_writes"
  ``check_number_property (\n live. n = -1 /\ live = LN) (Writes [1]) 0 (insert 1 () LN)``;
val _ = print_eval "cnp_signed_bound"
  ``check_number_property (\n live. -1 <= n) (Seq (Reads [1]) (Branch (Writes [2]) (Writes [3]))) 0 LN``;
val _ = print_eval "cnp_weak_branch"
  ``check_number_property (\n live. ~(n = -2 /\ lookup 2 live = SOME ())) (Branch (Writes [1]) (Reads [2])) 0 LN``;
val _ = print_eval "cnp_strong_branch"
  ``check_number_property_strong (\n live. ~(n = -2 /\ lookup 2 live = SOME ())) (Branch (Writes [1]) (Reads [2])) 0 LN``;
val _ = print_eval "cnp_strong_seq_live"
  ``check_number_property_strong (\n live. lookup 1 live = NONE \/ n = -1) (Seq (Reads [2]) (Reads [1])) 0 LN``;
val _ = print_simp "startlive_ok"
  ``check_startlive_prop (Writes [1]) 5 (insert 1 3 LN) (insert 1 7 LN) 0``;
val _ = print_simp "startlive_ndef"
  ``check_startlive_prop (Writes [1]) 5 LN (insert 1 7 LN) 6``;
val _ = print_simp "startlive_missing_end"
  ``check_startlive_prop (Writes [1]) 5 LN (insert 2 7 LN) 0``;
val _ = print_simp "startlive_branch_numbers"
  ``check_startlive_prop (Branch (Writes [1]) (Reads [])) 0 LN (insert 1 0 LN) (-1)``;
val _ = print_simp "registers_mem"
  ``2 IN live_tree_registers (Seq (Reads [1]) (Branch (Writes [2]) (Reads [])))``;
val _ = print_simp "registers_not_mem"
  ``3 IN live_tree_registers (Seq (Reads [1]) (Branch (Writes [2]) (Reads [])))``;
val _ = print_eval "intersect_touch"
  ``interval_intersect (-3, -1) (-1, 4)``;
val _ = print_eval "intersect_disjoint"
  ``interval_intersect (-3, -2) (-1, 4)``;
val _ = print_eval "point_inside"
  ``point_inside_interval (-3, -1) (-1)``;
val _ = print_eval "point_outside"
  ``point_inside_interval (-3, -1) 0``;
val _ = print_eval "the_some"
  ``THE (SOME (3:int)) = 3``;
val _ = print_prove "check_intervals_missing_end"
  ``check_intervals (K 0) (insert 1 0 (insert 2 5 LN)) (insert 1 1 LN)``
  (rw [check_intervals_def, interval_intersect_def] >>
   fs [lookup_insert] >> rpt (pop_assum mp_tac) >> rw [] >> intLib.COOPER_TAC);
val _ = print_prove "check_intervals_clash"
  ``~check_intervals (K 0) (insert 1 0 (insert 2 0 LN)) (insert 1 5 (insert 2 5 LN))``
  (rw [check_intervals_def, interval_intersect_def] >>
   qexists_tac `1` >> qexists_tac `2` >> EVAL_TAC);
