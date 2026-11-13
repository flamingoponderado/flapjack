(* Typed captures of the panSem state-accessor simplification lemmas
   (panSemScript.sml:422-429 kvar_simps, :476-487 is_valid_value_simps,
   :489-500 is_valid_value_simps2).  Each row prints the theorem's conclusion
   with inferred types (`show_types`) and its hypothesis count, so the
   finite-support-carrier Lean twins can be compared with the original
   `panSem$state` finite-map fields. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val _ = (print "kvar_simps_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panSemTheory.kvar_simps);
  print "\n");
val _ = print ("kvar_simps_hypotheses=" ^
  Int.toString (length (hyp panSemTheory.kvar_simps)) ^ "\n");

val _ = (print "is_valid_value_simps_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panSemTheory.is_valid_value_simps);
  print "\n");
val _ = print ("is_valid_value_simps_hypotheses=" ^
  Int.toString (length (hyp panSemTheory.is_valid_value_simps)) ^ "\n");

val _ = (print "is_valid_value_simps2_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panSemTheory.is_valid_value_simps2);
  print "\n");
val _ = print ("is_valid_value_simps2_hypotheses=" ^
  Int.toString (length (hyp panSemTheory.is_valid_value_simps2)) ^ "\n");
