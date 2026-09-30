(* Type evidence for the size-function domain in crep_inline
   `unreach_elim_prog_size` (crep_inlineProofScript.sml:1730-1733).

   `print_term` hides types, so this probe prints the elaborated type of the
   Datatype-generated `crepLang$prog_size` and the theorem statement with
   `show_types`, from the real CakeML `crep_inlineProofTheory`.  Regenerate with:

     CAKEML=<built CakeML checkout> \
       HOL_PROBE_ONLY=crep_inline_prog_size_type_probeScript.sml \
       scripts/hol-probes/regenerate.sh *)

load "bossLib";
load "preamble";
load "crep_inlineProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;

val () = print ("prog_size_type=" ^
  type_to_string (type_of (prim_mk_const {Thy = "crepLang", Name = "prog_size"})) ^ "\n");
val () = print ("exp_size_type=" ^
  type_to_string (type_of (prim_mk_const {Thy = "crepLang", Name = "exp_size"})) ^ "\n");
val () = show_types := true;
val () = (print "unreach_elim_prog_size_typed=";
  print_term (concl (fetch "crep_inlineProof" "unreach_elim_prog_size"));
  print "\n");
val () = show_types := false;
