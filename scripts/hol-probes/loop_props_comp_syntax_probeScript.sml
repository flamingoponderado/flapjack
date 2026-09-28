(* Direct HOL-EVAL observations of loopProps$comp_syntax_ok_def. *)
load "bossLib";
load "preamble";
load "loopPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopPropsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val live = ``insert 0 () LN``;
val _ = print_eval "comp_syntax_loop_positive"
  ``comp_syntax_ok ^live (loopLang$Loop ^live loopLang$Skip ^live)``;
val _ = print_eval "comp_syntax_loop_negative"
  ``comp_syntax_ok ^live (loopLang$Loop LN loopLang$Skip ^live)``;
val _ = print_eval "comp_syntax_seq_positive"
  ``comp_syntax_ok ^live (loopLang$Seq loopLang$Skip loopLang$Skip)``;
val _ = print_eval "comp_syntax_seq_negative"
  ``comp_syntax_ok ^live (loopLang$Seq
      (loopLang$Loop LN loopLang$Skip ^live) loopLang$Skip)``;
val _ = print_eval "comp_syntax_if_positive"
  ``comp_syntax_ok ^live (loopLang$If asm$Equal 1 (asm$Reg 2)
      loopLang$Skip loopLang$Skip ^live)``;
val _ = print_eval "comp_syntax_if_negative"
  ``comp_syntax_ok ^live (loopLang$If asm$Equal 1 (asm$Reg 2)
      loopLang$Skip loopLang$Skip LN)``;
