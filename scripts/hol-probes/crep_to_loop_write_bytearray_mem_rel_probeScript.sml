(*
  Direct HOL observations for the two sides of
  crep_to_loopProof$write_bytearray_mem_rel
  (cakeml/pancake/proofs/crep_to_loopProofScript.sml:251-256):
  panSem$write_bytearray (panSemScript.sml:309-316) and
  wordSem$write_bytearray (wordSemScript.sml) on the same address, byte list,
  domain and endianness, from wlab_wloc-related initial memories. Every
  address in the domain must satisfy wlab_wloc (pan result) = word result.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
load "wordSemTheory";
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
  end;

val pan_mem =
  ``(\a:64 word. if a = 8w then (Word (0x1122334455667788w:64 word) : 64 word_lab)
                 else (Word (0w:64 word) : 64 word_lab))``;
val word_mem =
  ``(\a:64 word. if a = 8w then (Word (0x1122334455667788w:64 word) : 64 word_loc)
                 else (Word (0w:64 word) : 64 word_loc))``;
val bytes = ``[(0xaaw:8 word); 0xbbw; 0xccw]``;
val dom_full = ``{8w:64 word; 16w}``;
val dom_part = ``{16w:64 word}``;

fun row label addr dom be =
  (print_eval (label ^ "_pan")
     ``panSem$write_bytearray (14w:64 word) ^bytes ^pan_mem ^dom ^be ^addr``;
   print_eval (label ^ "_word")
     ``wordSem$write_bytearray (14w:64 word) ^bytes ^word_mem ^dom ^be ^addr``);

val _ = row "le_full_8" ``8w:64 word`` dom_full ``F``;
val _ = row "le_full_16" ``16w:64 word`` dom_full ``F``;
val _ = row "be_full_8" ``8w:64 word`` dom_full ``T``;
val _ = row "be_full_16" ``16w:64 word`` dom_full ``T``;
val _ = row "le_part_16" ``16w:64 word`` dom_part ``F``;
val _ = row "le_part_8" ``8w:64 word`` dom_part ``F``;
