(* Direct original `check_clash_tree` oracle observations on small concrete
   clash trees with a numeric colour function and nonempty live/flive num_sets.
   Reference: cakeml/compiler/backend/reg_alloc/reg_allocScript.sml:1042-1081.
   The original checker lives in reg_allocScript.sml (word_alloc re-exports it);
   the real names are check_col / check_partial_col / check_clash_tree, and the
   colour argument has HOL type `num -> num` (not a finite map), the live and
   flive arguments are `num_set = unit spt`.  The colour function below is built
   from a finite map via FLOOKUP, i.e. a concrete numeric colour function. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;

(* Numeric colour function: 1|->1, 2|->2, 3|->3, 4|->4, everything else 0. *)
val colour =
  ``\n:num. case FLOOKUP ((FEMPTY : num |-> num) |+ (1,1) |+ (2,2) |+ (3,3) |+ (4,4)) n of
              NONE => (0:num) | SOME c => (c:num)``;
(* A colliding numeric colour function: 1|->1 and 2|->1. *)
val bad_colour =
  ``\n:num. case FLOOKUP ((FEMPTY : num |-> num) |+ (1,1) |+ (2,1)) n of
              NONE => (0:num) | SOME c => (c:num)``;

(* Delta writes/reads with a nonempty live and flive (live = flive = {3}). *)
val _ = print_eval "delta_live"
  ``check_clash_tree ^colour (Delta [1] [2])
      (sptree$insert 3 () sptree$LN) (sptree$insert 3 () sptree$LN) =
    SOME (sptree$insert 2 () (sptree$insert 3 () sptree$LN),
          sptree$insert 2 () (sptree$insert 3 () sptree$LN))``;

(* Fixed Set; live/flive are irrelevant to the Set clause. *)
val _ = print_eval "set_fixed"
  ``check_clash_tree ^colour (Set (sptree$insert 1 () sptree$LN))
      (sptree$insert 3 () sptree$LN) (sptree$insert 3 () sptree$LN) =
    SOME (sptree$insert 1 () sptree$LN, sptree$insert 1 () sptree$LN)``;

(* Branch with no fixed live set: the merged right-minus-left set is checked. *)
val _ = print_eval "branch_none"
  ``check_clash_tree ^colour (Branch NONE (Delta [] [1]) (Delta [] [2]))
      (sptree$insert 3 () sptree$LN) (sptree$insert 3 () sptree$LN) =
    SOME (sptree$insert 2 () (sptree$insert 1 () (sptree$insert 3 () sptree$LN)),
          sptree$insert 2 () (sptree$insert 1 () (sptree$insert 3 () sptree$LN)))``;

(* Branch with a fixed live set: the fixed set is checked with check_col. *)
val _ = print_eval "branch_some"
  ``check_clash_tree ^colour
      (Branch (SOME (sptree$insert 1 () sptree$LN)) (Delta [] []) (Delta [] []))
      (sptree$insert 3 () sptree$LN) (sptree$insert 3 () sptree$LN) =
    SOME (sptree$insert 1 () sptree$LN, sptree$insert 1 () sptree$LN)``;

(* Seq checks its right child first, then feeds the right outputs to the left. *)
val _ = print_eval "seq_right_first"
  ``check_clash_tree ^colour (Seq (Delta [2] []) (Delta [] [1]))
      (sptree$insert 3 () sptree$LN) (sptree$insert 3 () sptree$LN) =
    SOME (sptree$insert 1 () (sptree$insert 3 () sptree$LN),
          sptree$insert 1 () (sptree$insert 3 () sptree$LN))``;

(* Failure: the incoming flive already holds colour 1, so write 1 collides. *)
val _ = print_eval "delta_flive_collision"
  ``check_clash_tree ^colour (Delta [1] [])
      sptree$LN (sptree$insert 1 () sptree$LN) = NONE``;

(* Failure: bad_colour maps both 1 and 2 to 1, so the Set is not injective. *)
val _ = print_eval "set_colour_collision"
  ``check_clash_tree ^bad_colour
      (Set (sptree$insert 1 () (sptree$insert 2 () sptree$LN)))
      (sptree$insert 3 () sptree$LN) (sptree$insert 3 () sptree$LN) = NONE``;
