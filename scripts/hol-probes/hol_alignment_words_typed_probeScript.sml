(* Typed statements of the HOL `alignment` and `words` declarations ported in
   `Flapjack/Misc/Alignment.lean` and `Flapjack/Misc/Words/*.lean`, from the
   built HOL4 core theories (no rebuild). *)
load "alignmentTheory";
load "wordsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "align_def_typed=" alignmentTheory.align_def;
val _ = show_thm "aligned_def_typed=" alignmentTheory.aligned_def;
val _ = show_thm "byte_align_def_typed=" alignmentTheory.byte_align_def;
val _ = show_thm "byte_aligned_def_typed=" alignmentTheory.byte_aligned_def;
val _ = show_thm "aligned_add_sub_typed=" alignmentTheory.aligned_add_sub;
val _ = show_thm "word_slice_def_typed=" wordsTheory.word_slice_def;
val _ = show_thm "w2s_def_typed=" wordsTheory.w2s_def;
val _ = show_thm "word_to_hex_string_def_typed=" wordsTheory.word_to_hex_string_def;
val _ = show_thm "word_replicate_def_typed=" wordsTheory.word_replicate_def;
