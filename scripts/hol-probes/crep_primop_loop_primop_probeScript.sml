(* Direct HOL-EVAL oracle for the local crep_to_loopProof primitive-
   preservation theorem `crep_primop_loop_primop`
   (cakeml/pancake/proofs/crep_to_loopProofScript.sml:2337-2355).

   It evaluates the source `crepSem$crep_primop`, the target
   `loopSem$loop_primop` after `MAP crep_to_loopProof$wlab_wloc`, and the
   resulting preservation equation on concrete 8-bit `word_lab` payloads for
   the valid, overflow, nonzero-carry, short-arity, and long-arity cases. *)
load "bossLib";
load "preamble";
load "crepSemTheory";
load "loopSemTheory";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open loopSemTheory;
open crep_to_loopProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val valid_ws =
  ``[panSem$Word (3w : 8 word); panSem$Word (4w : 8 word);
     panSem$Word (2w : 8 word)]``;
val overflow_ws =
  ``[panSem$Word (255w : 8 word); panSem$Word (0w : 8 word);
     panSem$Word (1w : 8 word)]``;
val nonzero_carry_ws =
  ``[panSem$Word (255w : 8 word); panSem$Word (0w : 8 word);
     panSem$Word (7w : 8 word)]``;
val short_ws =
  ``[panSem$Word (3w : 8 word); panSem$Word (4w : 8 word)]``;
val long_ws =
  ``[panSem$Word (3w : 8 word); panSem$Word (4w : 8 word);
     panSem$Word (2w : 8 word); panSem$Word (0w : 8 word)]``;

val _ = print_eval "crep_valid"
  (``crep_primop AddCarry ^valid_ws``);
val _ = print_eval "loop_valid_mapped"
  (``loop_primop AddCarry (MAP wlab_wloc ^valid_ws)``);
val _ = print_eval "preserve_valid"
  (``(case crep_primop AddCarry ^valid_ws of
       SOME res_ws =>
         loop_primop AddCarry (MAP wlab_wloc ^valid_ws) = SOME (MAP wlab_wloc res_ws)
     | NONE => T)``);

val _ = print_eval "crep_overflow"
  (``crep_primop AddCarry ^overflow_ws``);
val _ = print_eval "loop_overflow_mapped"
  (``loop_primop AddCarry (MAP wlab_wloc ^overflow_ws)``);
val _ = print_eval "preserve_overflow"
  (``(case crep_primop AddCarry ^overflow_ws of
       SOME res_ws =>
         loop_primop AddCarry (MAP wlab_wloc ^overflow_ws) = SOME (MAP wlab_wloc res_ws)
     | NONE => T)``);

val _ = print_eval "crep_nonzero_carry"
  (``crep_primop AddCarry ^nonzero_carry_ws``);
val _ = print_eval "loop_nonzero_carry_mapped"
  (``loop_primop AddCarry (MAP wlab_wloc ^nonzero_carry_ws)``);
val _ = print_eval "preserve_nonzero_carry"
  (``(case crep_primop AddCarry ^nonzero_carry_ws of
       SOME res_ws =>
         loop_primop AddCarry (MAP wlab_wloc ^nonzero_carry_ws) =
           SOME (MAP wlab_wloc res_ws)
     | NONE => T)``);

val _ = print_eval "crep_invalid_two"
  (``crep_primop AddCarry ^short_ws``);
val _ = print_eval "preserve_invalid_two"
  (``(case crep_primop AddCarry ^short_ws of
       SOME res_ws =>
         loop_primop AddCarry (MAP wlab_wloc ^short_ws) = SOME (MAP wlab_wloc res_ws)
     | NONE => T)``);
val _ = print_eval "crep_invalid_four"
  (``crep_primop AddCarry ^long_ws``);
val _ = print_eval "preserve_invalid_four"
  (``(case crep_primop AddCarry ^long_ws of
       SOME res_ws =>
         loop_primop AddCarry (MAP wlab_wloc ^long_ws) = SOME (MAP wlab_wloc res_ws)
     | NONE => T)``);
val _ = print_eval "crep_primop_loop_primop_done" ``0``;
