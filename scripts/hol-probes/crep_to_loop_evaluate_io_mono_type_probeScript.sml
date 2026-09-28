(* Print the fully elaborated HOL type of the local LIST_CONJ helper used by
   code_rel_evaluate_call_correct. This is a source-shape probe, not an EVAL
   behavior fixture. Reference: crep_to_loopProofScript.sml:4066-4070. *)
load "bossLib";
load "preamble";
load "crepPropsTheory";
load "loopPropsTheory";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepPropsTheory;
open loopPropsTheory;
open crep_to_loopProofTheory;

val evaluate_io_mono_rephrases_probe =
  LIST_CONJ [
    Q.SPECL [`exs`, `s with clock := k`]
      crepPropsTheory.evaluate_add_clock_io_events_mono,
    Q.SPECL [`exs`, `s with clock := k`]
      loopPropsTheory.evaluate_add_clock_io_events_mono];

fun print_free_types label theorem =
  let
    val (left, right) = dest_conj (concl theorem)
    fun emit term =
      (print (label ^ "="); print_term term; print ":";
       print_type (type_of term); print "\n")
  in
    List.app emit (free_vars left);
    List.app emit (free_vars right)
  end;

val _ = print "evaluate_io_mono_rephrases_type=";
val _ = print_term (concl evaluate_io_mono_rephrases_probe);
val _ = print "\n";
val _ = print_free_types "free_variable" evaluate_io_mono_rephrases_probe;
val _ = print "crep_source_type=";
val _ = print_term (concl crepPropsTheory.evaluate_add_clock_io_events_mono);
val _ = print "\nloop_source_type=";
val _ = print_term (concl loopPropsTheory.evaluate_add_clock_io_events_mono);
val _ = print "\n";
