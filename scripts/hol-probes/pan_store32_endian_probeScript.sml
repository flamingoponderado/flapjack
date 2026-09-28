(* Direct HOL-EVAL probes for CakeML Pancake mem_store_32 in both endiannesses.
   Source: cakeml/pancake/semantics/panSemScript.sml mem_store_32_def (the
   exact Store32 clause passes `w2w w` for a word value w). *)
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

val _ = print_eval "store32_le_low"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {8w} F 8w 0x11223344w of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "store32_le_high"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {8w} F 12w 0x11223344w of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "store32_be_low"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {8w} T 8w 0x11223344w of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "store32_be_high"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {8w} T 12w 0x11223344w of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "store32_be_w2w"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {8w} T 8w ((w2w (0xAABBCCDD11223344w : word64)) : word32) of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "store32_be_unaligned"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {8w} T 9w 0x11223344w of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "store32_be_outside"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {16w} T 8w 0x11223344w of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
