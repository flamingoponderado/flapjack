(* Direct HOL-EVAL fixture for backend_common$word_shift (numeric dimindex).
   Reference: cakeml/compiler/backend/backend_commonScript.sml:157-164.
   word_shift (:'a) = if dimindex(:'a) = 32 then 2 else 3. *)
load "bossLib";
load "preamble";
load "backend_commonTheory";
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

val _ = print_eval "ws1" ``backend_common$word_shift (:1)``;
val _ = print_eval "ws4" ``backend_common$word_shift (:4)``;
val _ = print_eval "ws8" ``backend_common$word_shift (:8)``;
val _ = print_eval "ws16" ``backend_common$word_shift (:16)``;
val _ = print_eval "ws32" ``backend_common$word_shift (:32)``;
val _ = print_eval "ws64" ``backend_common$word_shift (:64)``;
val _ = print_eval "ws128" ``backend_common$word_shift (:128)``;
