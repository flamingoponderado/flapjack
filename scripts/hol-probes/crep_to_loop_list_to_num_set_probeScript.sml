(*
  Direct HOL-EVAL fixture for HOL sptree$list_to_num_set_def.
  Reference: HOL/src/finite_maps/sptreeScript.sml:2026-2028, the live-set
  builder used by crep_to_loopScript.sml:239 comp_func_def:
    (list_to_num_set [] = LN) /\
    (list_to_num_set (n::ns) = insert n () (list_to_num_set ns))

  The membership rows on [], [0], [0;1;2] and the unsorted [2;0;3] show which
  keys are present, and the final shape row exposes the right-recursive
  insertion `insert n () (list_to_num_set ns)` with LN as the base case.
*)
load "bossLib";
load "preamble";
load "sptreeTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open sptreeTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "ltns_nil_0"
  ``sptree$lookup 0 (sptree$list_to_num_set [] : num_set) = NONE``

val _ = print_eval "ltns_single_0"
  ``sptree$lookup 0 (sptree$list_to_num_set [0] : num_set) = SOME ()``

val _ = print_eval "ltns_three_0"
  ``sptree$lookup 0 (sptree$list_to_num_set [0;1;2] : num_set) = SOME ()``
val _ = print_eval "ltns_three_2"
  ``sptree$lookup 2 (sptree$list_to_num_set [0;1;2] : num_set) = SOME ()``
val _ = print_eval "ltns_three_3"
  ``sptree$lookup 3 (sptree$list_to_num_set [0;1;2] : num_set) = NONE``

val _ = print_eval "ltns_unsorted_2"
  ``sptree$lookup 2 (sptree$list_to_num_set [2;0;3] : num_set) = SOME ()``
val _ = print_eval "ltns_unsorted_0"
  ``sptree$lookup 0 (sptree$list_to_num_set [2;0;3] : num_set) = SOME ()``
val _ = print_eval "ltns_unsorted_3"
  ``sptree$lookup 3 (sptree$list_to_num_set [2;0;3] : num_set) = SOME ()``
val _ = print_eval "ltns_unsorted_4"
  ``sptree$lookup 4 (sptree$list_to_num_set [2;0;3] : num_set) = NONE``

val _ = print_eval "ltns_cons_shape"
  ``sptree$list_to_num_set (2::[0;3]) =
      sptree$insert 2 () (sptree$list_to_num_set [0;3])``

val _ = print_eval "done" ``T``