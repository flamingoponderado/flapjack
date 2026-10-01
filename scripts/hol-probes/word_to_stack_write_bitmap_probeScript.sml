load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of `write_bitmap_def`, the finite-map/`toAList`-ordered bitmap
   builder that `wLive` feeds into the Word-to-Stack `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709).  Defined at
   cakeml/compiler/backend/word_to_stackScript.sml:240-244:

     (write_bitmap live k f'):'a word list =
       let names = MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList live) in
         word_list (GENLIST (\x. MEM x names) f' ++ [T]) (dimindex (:'a) - 1)

   `write_bitmap` is payload-polymorphic in its Spt input; these fixtures
   specialize it to unit-valued `num_set`. The exact generic-Spt Lean port
   is WordToStack/LiveBitmap.lean::writeBitmapExact. The rows below
   isolate the finite-map/ordering prerequisite and, in particular, show the
   result depends only on the *domain* of `live` (insertion order is
   unobservable because `write_bitmap` reads `toAList live` only through `MEM`).

   Provenance (bead flapjack-pxn.18.5.15.3.5): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_write_bitmap_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "wb_empty"
  ``(word_to_stack$write_bitmap (sptree$list_to_num_set []) 0 4) : word8 list``;
val _ = print_eval "wb_single"
  ``(word_to_stack$write_bitmap (sptree$list_to_num_set [0]) 0 4) : word8 list``;
val _ = print_eval "wb_two"
  ``(word_to_stack$write_bitmap (sptree$list_to_num_set [0;1]) 0 4) : word8 list``;
val _ = print_eval "wb_offset"
  ``(word_to_stack$write_bitmap (sptree$list_to_num_set [2;4;6]) 0 8) : word8 list``;
val _ = print_eval "wb_boundary"
  ``(word_to_stack$write_bitmap (sptree$list_to_num_set [0;2;4]) 0 64) : word64 list``;
val _ = print_eval "wb_order_a"
  ``(word_to_stack$write_bitmap (sptree$list_to_num_set [0;1;2]) 0 8) : word8 list``;
val _ = print_eval "wb_order_b"
  ``(word_to_stack$write_bitmap (sptree$list_to_num_set [2;0;1]) 0 8) : word8 list``;
val _ = print_eval "wb_order_eq"
  ``((word_to_stack$write_bitmap (sptree$list_to_num_set [0;1;2]) 0 8 : word8 list) =
     (word_to_stack$write_bitmap (sptree$list_to_num_set [2;0;1]) 0 8 : word8 list))``;

val _ = print_eval "wb_payload_nat"
  ``(word_to_stack$write_bitmap (sptree$fromAList [(0,37:num);(2,99)]) 0 8) : word8 list``;
val _ = print_eval "wb_payload_bool"
  ``(word_to_stack$write_bitmap (sptree$fromAList [(0,T);(2,F)]) 0 8) : word8 list``;
