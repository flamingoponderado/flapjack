(* Direct original HOL-EVAL rows for crep_to_loop$comp_func_def. *)
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

val _ = print_eval "comp_func_skip"
  ``comp_func RISC_V FEMPTY [] (Skip : 8 word crepLang$prog)``;
val _ = print_eval "comp_func_one_parameter_return"
  ``comp_func RISC_V FEMPTY [5] (Return [Var 5] : 8 word crepLang$prog)``;
val _ = print_eval "comp_func_pair_parameter_return"
  ``comp_func RISC_V FEMPTY [5; 7]
      (Return [Var 5; Var 7] : 8 word crepLang$prog)``;
val _ = print_eval "comp_func_duplicate_parameters"
  ``comp_func RISC_V FEMPTY [5; 5] (Return [Var 5] : 8 word crepLang$prog)``;
val _ = print_eval "comp_func_if_cutset"
  ``comp_func RISC_V FEMPTY [5; 7; 9]
      (crepLang$If (crepLang$Const (1w : 8 word))
        crepLang$Skip crepLang$Skip)``;
