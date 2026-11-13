(* Direct HOL-EVAL probes for CakeML Pancake panProps shape_of_val and
   res_var FLOOKUP lemmas (panPropsScript.sml:14, :220, :228, :236). *)
load "bossLib";
load "preamble";
load "panSemTheory";
load "panPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val locals = ``(FEMPTY |+ ("x", ValWord (3w : 64 word)))``

val _ = print_eval "spv_one"
  ``shape_of (ValWord (5w : 64 word))``
val _ = print_eval "rv_hit"
  ``FLOOKUP (res_var ^locals ("x", SOME (ValWord (7w : 64 word)))) "x"``
val _ = print_eval "rv_miss"
  ``FLOOKUP (res_var ^locals ("y", SOME (ValWord (7w : 64 word)))) "x"``
val _ = print_eval "rv_diff"
  ``(FLOOKUP (res_var ^locals ("y", NONE)) "x" = FLOOKUP ^locals "x")``
val _ = print_eval "rv_some"
  ``(FLOOKUP (res_var ^locals ("x", FLOOKUP ^locals "x")) "x" =
     FLOOKUP ^locals "x")``

(* Capture the exported HOL theorem with its inferred word-label carrier. *)
val _ = (print "shape_of_val_typed=";
  Lib.with_flag (Globals.show_types, true) print_term (concl panPropsTheory.shape_of_val);
  print "\n");
val _ = print ("shape_of_val_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.shape_of_val)) ^ "\n");

val _ = (print "word_constructor_typed=";
  Lib.with_flag (Globals.show_types, true) print_type (type_of ``panSem$Word``);
  print "\n");
val _ = (print "value_constructors_typed=";
  List.app (fn tm => (Lib.with_flag (Globals.show_types, true) print_type (type_of tm); print ";"))
    [``panSem$Val``, ``panSem$RStruct``, ``panSem$NStruct``];
  print "\n");
val _ = (print "shape_of_def_typed=";
  Lib.with_flag (Globals.show_types, true) print_term (concl panSemTheory.shape_of_def);
  print "\n");

(* Typed statements of the two res_var lookup lemmas. *)
val _ = (print "flookup_res_var_some_eq_lookup_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.flookup_res_var_some_eq_lookup);
  print "\n");
val _ = print ("flookup_res_var_some_eq_lookup_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.flookup_res_var_some_eq_lookup)) ^ "\n");
val _ = (print "flookup_res_var_diff_eq_org_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.flookup_res_var_diff_eq_org);
  print "\n");
val _ = print ("flookup_res_var_diff_eq_org_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.flookup_res_var_diff_eq_org)) ^ "\n");
