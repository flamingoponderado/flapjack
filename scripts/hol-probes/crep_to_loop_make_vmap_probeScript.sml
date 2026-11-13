(* Typed capture of HOL crep_to_loop make_vmap_def (crep_to_loopScript.sml:230-233). *)
load "bossLib";
load "preamble";
load "crep_to_loopTheory";
open bossLib;
open HolKernel Parse;
open preamble;

val _ = (print "make_vmap_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl crep_to_loopTheory.make_vmap_def);
  print "\n");
val _ = print ("make_vmap_def_hypotheses=" ^
  Int.toString (length (hyp crep_to_loopTheory.make_vmap_def)) ^ "\n");
