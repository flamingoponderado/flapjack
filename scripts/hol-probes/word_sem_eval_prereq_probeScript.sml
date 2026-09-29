(*
  Direct HOL-EVAL fixture for the wordSem evaluate_def prerequisites of bead
  flapjack-h29l.8.1: misc$shift_seq (Flapjack/Misc/ShiftSeq.lean) and the
  sptree domain set conditions rendered by sptDomainEmpty / sptDomainEqUnion
  (Flapjack/Compiler/Backend/Semantics/WordSem/Domain.lean).
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val _ = print_eval "shift_seq" ``shift_seq 2 (\i:num. i * 10) 3``;
val _ = print_eval "shift_seq_zero" ``shift_seq 0 (\i:num. i + 7) 4``;
val _ = print_eval "dom_empty_ln" ``domain (LN : num_set) = {}``;
val _ = print_eval "dom_empty_one" ``domain (insert 3 () LN : num_set) = {}``;
val _ = print_eval "dom_union_eq"
  ``domain (fromAList [(1:num, 5:num); (2, 6)]) = domain (insert 1 () LN : num_set) UNION domain (insert 2 () LN : num_set)``;
val _ = print_eval "dom_union_extra"
  ``domain (fromAList [(1:num, 5:num); (2, 6); (4, 7)]) = domain (insert 1 () LN : num_set) UNION domain (insert 2 () LN : num_set)``;
val _ = print_eval "dom_union_missing"
  ``domain (fromAList [(1:num, 5:num)]) = domain (insert 1 () LN : num_set) UNION domain (insert 2 () LN : num_set)``;
