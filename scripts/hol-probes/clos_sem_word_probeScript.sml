load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "word_app_typed=" closSemTheory.do_word_app_def;
val _ = show_eval "byte_add_wrap=" ``closSem$do_word_app (WordOpw W8 Add) [Number 255; Number 2]``;
val _ = show_eval "byte_negative=" ``closSem$do_word_app (WordOpw W8 Add) [Number (-1); Number 2]``;
val _ = show_eval "byte_too_large=" ``closSem$do_word_app (WordFromWord F) [Number 256]``;
val _ = show_eval "byte_asr=" ``closSem$do_word_app (WordShift W8 Asr 7) [Number 128]``;
val _ = show_eval "word_from_negative=" ``closSem$do_word_app WordFromInt [Number (-1)]``;
val _ = show_eval "word_to_byte=" ``closSem$do_word_app (WordFromWord T) [Word64 511w]``;
val _ = show_eval "byte_compare=" ``closSem$do_word_app (WordTest W8 (Compare Lt)) [Number 127; Number 128]``;
val _ = show_eval "byte_alt_compare=" ``closSem$do_word_app (WordTest W8 (AltCompare Lt)) [Number 1; Number 2]``;
val _ = show_eval "word_add=" ``closSem$do_word_app (WordOpw W64 Add) [Word64 5w; Word64 9w]``;
val _ = show_eval "word_shift=" ``closSem$do_word_app (WordShift W64 Lsl 3) [Word64 7w]``;
