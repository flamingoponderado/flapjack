(* Direct HOL capture of the generated panSem$evaluate_ind principle. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val _ = print "evaluate_ind=";
val _ = print_term (concl evaluate_ind);
val _ = print "\n";
