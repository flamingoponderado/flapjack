(* Direct HOL-EVAL fixture for loop_live$optimise. *)
load "bossLib";
load "preamble";
load "loop_liveTheory";
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

val _ = print_eval "skip"
  ``loop_live$optimise
      (loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "loc_value"
  ``loop_live$optimise
      (loopLang$LocValue 3 7 : 8 word loopLang$prog)``;
val _ = print_eval "seq"
  ``loop_live$optimise
      (loopLang$Seq loopLang$Skip loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "ffi"
  ``loop_live$optimise
      (loopLang$FFI «f» 1 2 3 4 LN : 8 word loopLang$prog)``;

val live_one = ``(sptree$fromAList [(1:num,())] : sptree$num_set)``;
val _ = print_eval "loop_fixedpoint_iter"
  ``loop_live$fixedpoint [] ^live_one LN ^live_one
      (loopLang$Return [1] : 8 word loopLang$prog)``;
val _ = print_eval "fixedpoint_none_fallback"
  ``loop_live$fixedpoint [] ^live_one ^live_one LN
      (loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "shrink_loop_fixedpoint"
  ``loop_live$shrink []
      (loopLang$Loop ^live_one
        (loopLang$Return [1] : 8 word loopLang$prog) LN) LN``;
