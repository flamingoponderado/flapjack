(* Direct HOL-EVAL probes for CakeML Pancake Loop fix_clock_def. *)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:('a,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "fix_clock_lower_new"
  ``(SND (fix_clock (^s with clock := 10)
      (Result [], (^s with clock := 4)))).clock``
val _ = print_eval "fix_clock_lower_old"
  ``(SND (fix_clock (^s with clock := 4)
      (Result [], (^s with clock := 10)))).clock``
val _ = print_eval "fix_clock_zero"
  ``(SND (fix_clock (^s with clock := 0)
      (Result [], (^s with clock := 0)))).clock``

(* Typed capture of the two-state fix_clock_def (task 167). *)
val _ = (print "fix_clock_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl loopSemTheory.fix_clock_def);
  print "\n");
val _ = print ("fix_clock_def_hypotheses=" ^
  Int.toString (length (hyp loopSemTheory.fix_clock_def)) ^ "\n");
