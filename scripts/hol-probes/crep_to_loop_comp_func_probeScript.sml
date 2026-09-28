(*
  Direct HOL-EVAL fixture for Pancake crep_to_loop comp_func_def.
  Reference: cakeml/pancake/crep_to_loopScript.sml:235-241.
  The observations cover an empty program, a program with a make_vmap entry
  (so the vmax/live/var lookup path is exercised), and a missing global
  function reference.
*)
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
  end

val _ = print_eval "comp_func_skip"
  ``comp_func RISC_V (FEMPTY : (mlstring |-> (num # num))) []
      (crepLang$Skip : 8 word crepLang$prog)``

val _ = print_eval "comp_func_return_var"
  ``comp_func RISC_V (FEMPTY : (mlstring |-> (num # num))) [0]
      (crepLang$Return [crepLang$Var 0] : 8 word crepLang$prog)``

val _ = print_eval "comp_func_two_params"
  ``comp_func RISC_V (FEMPTY : (mlstring |-> (num # num))) [0; 1]
      (crepLang$Return [crepLang$Var 1] : 8 word crepLang$prog)``

val _ = print_eval "done" ``T``