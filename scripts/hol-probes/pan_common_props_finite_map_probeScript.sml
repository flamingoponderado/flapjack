(* Typed original statements for the pan_commonProps finite-map predicates and
   the zip/FUPDATE_LIST lookup lemma (pan_commonPropsScript.sml:8-24, :244-251).
   These captures support source review of the exact-carrier Lean twins; they do
   not establish HOL-to-Lean equivalence. *)
load "bossLib";
load "preamble";
load "pan_commonPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_commonPropsTheory;

val _ = (print "ctxt_max_def_typed=";
  Lib.with_flag (Globals.show_types, true) print_term (concl ctxt_max_def);
  print "\n");
val _ = (print "ctxt_max_def_hypotheses=";
  print (Int.toString (length (hyp ctxt_max_def))); print "\n");

val _ = (print "no_overlap_def_typed=";
  Lib.with_flag (Globals.show_types, true) print_term (concl no_overlap_def);
  print "\n");
val _ = (print "no_overlap_def_hypotheses=";
  print (Int.toString (length (hyp no_overlap_def))); print "\n");

val _ = (print "update_eq_zip_flookup_typed=";
  Lib.with_flag (Globals.show_types, true) print_term (concl update_eq_zip_flookup);
  print "\n");
val _ = (print "update_eq_zip_flookup_hypotheses=";
  print (Int.toString (length (hyp update_eq_zip_flookup))); print "\n");
