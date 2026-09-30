(* Direct HOL capture of the generated panSem$eval_ind (expression-level)
   induction principle. Records the exact recursive IH binders and side
   conditions (notably the Load shape-wf guard) for source review of the
   pan_globals compile_exp_correct case ports. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val _ = print "eval_ind=";
val _ = print_term (concl eval_ind);
val _ = print "\n";
