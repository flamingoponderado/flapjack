(* Direct inspection of the proved Cake semanticsProps implements'_trans theorem.
   Reference: cakeml/semantics/proofs/semanticsPropsScript.sml:285-295. *)
load "bossLib";
load "semanticsPropsTheory";
open bossLib HolKernel Parse semanticsPropsTheory;

val _ = print "implements_prime_trans=";
val _ = print_term (concl implements'_trans);
val _ = print "\n";

val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "prog_events_determ="; print_thm evaluate_prog_events_determ; print "\n");
val _ = (print "prog_io_events_chain="; print_thm evaluate_prog_io_events_chain; print "\n");
val _ = (print "semantics_prog_total="; print_thm semantics_prog_total; print "\n");
