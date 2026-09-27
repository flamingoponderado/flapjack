(* Direct original HOL-EVAL rows for pan_to_crep$comp_func_def
   (cakeml/pancake/pan_to_crepScript.sml:337-343). *)
load "bossLib";
load "preamble";
load "pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val fs = ``(FEMPTY : mlstring |-> ((mlstring # panLang$shape) list # panLang$shape))``;
val eids = ``(FEMPTY : mlstring |-> 8 word)``;

val _ = print_eval "comp_func_skip"
  ``pan_to_crep$comp_func ^fs ^eids [] (panLang$Skip : 8 panLang$prog)``;

val _ = print_eval "comp_func_one_parameter_return"
  ``pan_to_crep$comp_func ^fs ^eids [(«x», panLang$One)]
      (panLang$Return (panLang$Var panLang$Local «x»))``;

val _ = print_eval "comp_func_pair_parameter_return"
  ``pan_to_crep$comp_func ^fs ^eids
      [(«pair», panLang$Comb [panLang$One; panLang$One])]
      (panLang$Return (panLang$Var panLang$Local «pair»))``;
