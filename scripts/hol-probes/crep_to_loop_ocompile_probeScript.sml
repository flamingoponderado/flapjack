(* Direct HOL-EVAL cases for crep_to_loop$ocompile_def
   (`ocompile ctxt l p = (loop_live$optimise o compile ctxt l) p`). *)
load "bossLib";
load "preamble";
load "crep_to_loopTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val ctxt = ``context
  (FEMPTY |+ (1, 7) |+ (2, 8) |+ (3, 9) |+ (4, 10))
  (FEMPTY |+ (strlit "f", (42, 2))) 4 RISC_V``;
val live = ``insert 2 () (insert 1 () LN)``;

val _ = print_eval "ocompile_skip"
  ``ocompile ^ctxt ^live (crepLang$Skip : 8 word crepLang$prog)``;
val _ = print_eval "ocompile_tick"
  ``ocompile ^ctxt ^live (crepLang$Tick : 8 word crepLang$prog)``;
val _ = print_eval "ocompile_assign"
  ``ocompile ^ctxt ^live
      (crepLang$Assign 1 (crepLang$Var 2) : 8 word crepLang$prog)``;
val _ = print_eval "ocompile_primitive"
  ``ocompile ^ctxt ^live
      (crepLang$Primitive [1] panLang$AddCarry [2] : 8 word crepLang$prog)``;
val _ = print_eval "ocompile_return"
  ``ocompile ^ctxt ^live
      (crepLang$Return [crepLang$Const (5w : 8 word)])``;
val _ = print_eval "ocompile_call"
  ``ocompile ^ctxt ^live
      (crepLang$Call (SOME ([1], SOME (3w, crepLang$Break 7))) (strlit "f")
        [crepLang$Const (16w : 8 word)])``;
