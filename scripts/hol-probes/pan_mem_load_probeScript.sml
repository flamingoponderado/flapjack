(*
  Direct HOL-EVAL probes for CakeML Pancake panSem$mem_load.
  The output is checked into pan_mem_load_probe.out and is consumed by Lean
  parity tests; this script is not a second implementation.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "one_hit"
  ``mem_load One (10w : 64 word) {10w}
      (\a : 64 word. Word 3w) []``
(* This row aligns the source Load input/value with compile_exp's `load_one`
   and the Crep evaluator's generated Load regression. *)
val _ = print_eval "one_load_one"
  ``mem_load One (3w : 64 word) {3w}
      (\a : 64 word. Word 3w) []``
val _ = print_eval "one_miss"
  ``mem_load One (11w : 64 word) {10w}
      (\a : 64 word. Word 3w) []``
val _ = print_eval "comb_hit"
  ``mem_load (Comb [One; One]) (10w : 64 word) {10w;18w}
      (\a : 64 word. if a = 10w then Word 3w else Word 5w) []``
val _ = print_eval "named_hit"
  ``mem_load (Named (strlit "Pair")) (10w : 64 word) {10w;18w}
      (\a : 64 word. if a = 10w then Word 3w else Word 5w)
      [(strlit "Pair", <| fields := [(strlit "left", One);
                                      (strlit "right", One)]; size := 2 |>)]``
val _ = print_eval "named_suffix_blocked"
  ``mem_load (Named (strlit "Outer")) (10w : 64 word) {10w}
      (\a : 64 word. Word 3w)
      [(strlit "Later", <| fields := []; size := 1 |>);
       (strlit "Outer", <| fields := [(strlit "later", Named (strlit "Later"))];
                             size := 1 |>)]``
(* Recursive rows used by the production-vs-exact flat-load bridge. The
   second word begins at bytes_in_word * size_of_sh_with_ctxt [] One = 8. *)
val _ = print_eval "recursive_mem_loads_two_words"
  ``mem_loads [One; One] (0w : 64 word) {0w; 8w}
      (\a : 64 word. if a = 0w then Word 17w else Word 34w) []``
val _ = print_eval "recursive_comb_two_words"
  ``mem_load (Comb [One; One]) (0w : 64 word) {0w; 8w}
      (\a : 64 word. if a = 0w then Word 17w else Word 34w) []``
val _ = print_eval "recursive_named_two_fields"
  ``mem_load (Named (strlit "S")) (0w : 64 word) {0w; 8w}
      (\a : 64 word. if a = 0w then Word 17w else Word 34w)
      [(strlit "S", <| fields := [(strlit "f", One); (strlit "g", One)];
                       size := 2 |>)]``
