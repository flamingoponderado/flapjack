(* Typed captures for the Phase-4 exact ports (task 145).
   Reference: panSemScript.sml:437-439 (empty_locals), 458-467 (lookup_code),
   510-527 (sh_mem_load); pan_to_crepScript.sml:310-316 (mk_ctxt), 366-374
   (make_funcs), 393-397 (compile_prog);
   pan_to_crepProofScript.sml:4139-4176 (evaluate_nested_decs_load_globals). *)
load "bossLib";
load "preamble";
load "panSemTheory";
load "pan_to_crepTheory";
load "pan_to_crepProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;
open pan_to_crepTheory;
open pan_to_crepProofTheory;

val _ = (print "empty_locals_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panSemTheory.empty_locals_def);
  print "\n");
val _ = print ("empty_locals_def_hypotheses=" ^
  Int.toString (length (hyp panSemTheory.empty_locals_def)) ^ "\n");

val _ = (print "lookup_code_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panSemTheory.lookup_code_def);
  print "\n");
val _ = print ("lookup_code_def_hypotheses=" ^
  Int.toString (length (hyp panSemTheory.lookup_code_def)) ^ "\n");

val _ = (print "sh_mem_load_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panSemTheory.sh_mem_load_def);
  print "\n");
val _ = print ("sh_mem_load_def_hypotheses=" ^
  Int.toString (length (hyp panSemTheory.sh_mem_load_def)) ^ "\n");

val _ = (print "mk_ctxt_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl pan_to_crepTheory.mk_ctxt_def);
  print "\n");
val _ = print ("mk_ctxt_def_hypotheses=" ^
  Int.toString (length (hyp pan_to_crepTheory.mk_ctxt_def)) ^ "\n");

val _ = (print "make_funcs_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl pan_to_crepTheory.make_funcs_def);
  print "\n");
val _ = print ("make_funcs_def_hypotheses=" ^
  Int.toString (length (hyp pan_to_crepTheory.make_funcs_def)) ^ "\n");

val _ = (print "compile_prog_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl pan_to_crepTheory.compile_prog_def);
  print "\n");
val _ = print ("compile_prog_def_hypotheses=" ^
  Int.toString (length (hyp pan_to_crepTheory.compile_prog_def)) ^ "\n");

val _ = (print "evaluate_nested_decs_load_globals_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl pan_to_crepProofTheory.evaluate_nested_decs_load_globals);
  print "\n");
val _ = print ("evaluate_nested_decs_load_globals_hypotheses=" ^
  Int.toString (length (hyp pan_to_crepProofTheory.evaluate_nested_decs_load_globals)) ^ "\n");

val _ = (print "globals_lookup_def_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl pan_to_crepProofTheory.globals_lookup_def);
  print "\n");
val _ = print ("globals_lookup_def_hypotheses=" ^
  Int.toString (length (hyp pan_to_crepProofTheory.globals_lookup_def)) ^ "\n");

val _ = print "pan_phase4_exact_probe_done\n";
