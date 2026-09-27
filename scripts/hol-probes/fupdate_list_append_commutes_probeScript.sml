(* Direct HOL evaluations for finite_mapTheory.FUPDATE_LIST_APPEND_COMMUTES
   (HOL/src/finite_maps/finite_mapScript.sml:2960), used by
   pan_to_crepProofScript.sml at lines 1001 and 1197.

   The disjoint row checks the theorem's key-set premise and swapped update
   result. The overlap rows demonstrate why the premise is required. *)
load "bossLib";
load "finite_mapTheory";
load "boolSyntax";
open bossLib;
open HolKernel Parse;
open boolSyntax;
open finite_mapTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=" ^ term_to_string (rhs (concl th)) ^ "\n")
  end;

val l1 = ``[(1, 10); (2, 20)] : (num # num) list``;
val l2 = ``[(3, 30)] : (num # num) list``;
val overlap = ``[(1, 99)] : (num # num) list``;
val fm = ``((FEMPTY |+ (4, 40)) : (num, num) fmap)``;

val _ = print ("source_theorem=" ^ term_to_string (concl FUPDATE_LIST_APPEND_COMMUTES) ^ "\n");

val _ = print_eval "disjoint_keys"
  (``DISJOINT (set (MAP FST ^l1)) (set (MAP FST ^l2))``);
val _ = print_eval "disjoint_commutes"
  (``(^fm |++ ^l1 |++ ^l2 = ^fm |++ ^l2 |++ ^l1)``);
val _ = print_eval "disjoint_lookup_preserved"
  (``FLOOKUP (^fm |++ ^l1 |++ ^l2) 4``);
val _ = print_eval "disjoint_lookup_equal"
  (``FLOOKUP (^fm |++ ^l1 |++ ^l2) 1 =
     FLOOKUP (^fm |++ ^l2 |++ ^l1) 1``);

val _ = print_eval "overlap_keys_disjoint"
  (``DISJOINT (set (MAP FST ^l1)) (set (MAP FST ^overlap))``);
val _ = print_eval "overlap_order_changes_map"
  (``(^fm |++ ^l1 |++ ^overlap = ^fm |++ ^overlap |++ ^l1)``);
val _ = print_eval "overlap_guarded_implication"
  (``DISJOINT (set (MAP FST ^l1)) (set (MAP FST ^overlap)) ==>
     (^fm |++ ^l1 |++ ^overlap = ^fm |++ ^overlap |++ ^l1)``);
val _ = print_eval "overlap_left_lookup"
  (``FLOOKUP (^fm |++ ^l1 |++ ^overlap) 1``);
val _ = print_eval "overlap_right_lookup"
  (``FLOOKUP (^fm |++ ^overlap |++ ^l1) 1``);
val _ = print_eval "overlap_lookup_equal"
  (``FLOOKUP (^fm |++ ^l1 |++ ^overlap) 1 =
     FLOOKUP (^fm |++ ^overlap |++ ^l1) 1``);
