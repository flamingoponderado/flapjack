load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
open source_to_flatProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "abort_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl abort_def); print "\n");
val _ = (print "compile_correct_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_correct); print "\n");
val _ = (print "compile_prog_correct_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_prog_correct); print "\n");
val _ = (print "compile_prog_semantics_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_prog_semantics); print "\n");
