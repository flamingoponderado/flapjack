(* Direct original-HOL observations of misc$lookup_any and misc$find_index.

   lookup_any (miscScript.sml:344-350) is `lookup x sp` with a default on NONE;
   find_index (miscScript.sml:1055-1058) is the literal first-match search with
   a starting offset.  Used by bead flapjack-pxn.18.5.15.10.10. *)
load "preamble";
load "miscTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open miscTheory;

val print_eval = fn label => fn q =>
  (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");

(* lookup_any: hit, hit at key 0, miss with default, and empty map. *)
val _ = print_eval "lu_hit"
  ``lookup_any 2 (fromList2 [10;20;30] : num spt) 99``;
val _ = print_eval "lu_hit_zero"
  ``lookup_any 0 (fromList2 [10;20;30] : num spt) 99``;
val _ = print_eval "lu_miss_default"
  ``lookup_any 1 (fromList2 [10;20;30] : num spt) 99``;
val _ = print_eval "lu_empty_default"
  ``lookup_any 0 (fromList2 ([] : num list)) 7``;

(* find_index: hit at 0, hit later, miss, and earlier duplicate. *)
val _ = print_eval "fi_zero"
  ``find_index 0 ([0;0] : num list) 0``;
val _ = print_eval "fi_middle"
  ``find_index 2 ([1;2;3] : num list) 7``;
val _ = print_eval "fi_absent"
  ``find_index 2 ([1;3] : num list) 7``;
val _ = print_eval "fi_duplicate"
  ``find_index 2 ([1;2;2] : num list) 3``;
