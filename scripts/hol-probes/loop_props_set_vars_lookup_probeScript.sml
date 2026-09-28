(* Direct HOL-EVAL probes for CakeML Pancake Loop set_vars lookup properties
   (loopPropsScript.sml lookup_set_vars and lookup_set_vars_not_MEM, with
   loopSemScript.sml set_vars_def).  The base locals tree is concrete so that
   sptree lookup/insert reduce under EVAL. *)
load "bossLib";
load "preamble";
load "loopPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopPropsTheory;
open loopSemTheory;

val s = ``(s:(8,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val base = ``(insert 5 (Word (2w:8 word)) (insert 9 (Word (1w:8 word)) LN) :
              8 word_loc sptree$num_map)``;
val st = ``(^s with locals := ^base)``;

val _ = print_eval "set_vars_lookup_hit"
  ``lookup 3 (set_vars [3;4] [Word (7w:8 word); Word (8w:8 word)] ^st).locals``
val _ = print_eval "set_vars_lookup_hit2"
  ``lookup 4 (set_vars [3;4] [Word (7w:8 word); Word (8w:8 word)] ^st).locals``
val _ = print_eval "set_vars_lookup_base"
  ``lookup 9 (set_vars [3;4] [Word (7w:8 word); Word (8w:8 word)] ^st).locals``
val _ = print_eval "set_vars_lookup_other"
  ``lookup 5 (set_vars [3;4] [Word (7w:8 word); Word (8w:8 word)] ^st).locals``
val _ = print_eval "set_vars_lookup_miss"
  ``lookup 6 (set_vars [3;4] [Word (7w:8 word); Word (8w:8 word)] ^st).locals``
val _ = print_eval "set_vars_lookup_dup"
  ``lookup 3 (set_vars [3;3] [Word (7w:8 word); Word (8w:8 word)] ^st).locals``
val _ = print_eval "set_vars_lookup_zip_short"
  ``lookup 4 (set_vars [3;4] [Word (7w:8 word)] ^st).locals``
val _ = print_eval "lookup_set_vars_not_mem_eq"
  ``(lookup 6 (set_vars [3;4] [Word (7w:8 word); Word (8w:8 word)] ^st).locals =
    lookup 6 (^st).locals)``
val _ = print_eval "lookup_set_vars_match_eq"
  ``(lookup 3 (set_vars [3;4] [Word (7w:8 word); Word (8w:8 word)] ^st).locals =
    case ALOOKUP (ZIP ([3;4],[Word (7w:8 word); Word (8w:8 word)])) 3 of
      NONE => lookup 3 (^st).locals
    | SOME v => SOME v)``