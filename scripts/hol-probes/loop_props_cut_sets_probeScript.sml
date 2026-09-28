(* Direct HOL-EVAL observations of loopProps$cut_sets_def clauses. *)
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

val _ = print_eval "cut_sets_skip"
  ``cut_sets (insert 8 () LN) (loopLang$Skip)``;
val _ = print_eval "cut_sets_locvalue"
  ``cut_sets (insert 8 () LN) (loopLang$LocValue 3 4)``;
val _ = print_eval "cut_sets_assign"
  ``cut_sets (insert 8 () LN) (loopLang$Assign 4 (loopLang$Const (0w : 8 word)))``;
val _ = print_eval "cut_sets_load32"
  ``cut_sets (insert 8 () LN) (loopLang$Load32 5 6)``;
val _ = print_eval "cut_sets_loadbyte"
  ``cut_sets (insert 8 () LN) (loopLang$LoadByte 7 9)``;
val _ = print_eval "cut_sets_seq"
  ``cut_sets (insert 8 () LN)
      (loopLang$Seq (loopLang$LocValue 1 2)
                    (loopLang$Assign 2 (loopLang$Const (0w : 8 word))))``;
val _ = print_eval "cut_sets_if"
  ``cut_sets (insert 8 () LN)
      (loopLang$If asm$Equal 1 (asm$Reg 2) loopLang$Skip loopLang$Tick
        (insert 9 () LN))``;
val _ = print_eval "cut_sets_longdiv"
  ``cut_sets (insert 8 () LN) (loopLang$Arith (loopLang$LLongDiv 1 2 3 4 5))``;
val _ = print_eval "cut_sets_longmul"
  ``cut_sets (insert 8 () LN) (loopLang$Arith (loopLang$LLongMul 3 4 5 6))``;
val _ = print_eval "cut_sets_div"
  ``cut_sets (insert 8 () LN) (loopLang$Arith (loopLang$LDiv 7 8 9))``;
val _ = print_eval "cut_sets_catch_all"
  ``cut_sets (insert 8 () LN) (loopLang$Break 11)``;
