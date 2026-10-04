(* Exported original-theory capture of compilerScript pancake_backend_conf_def (744-747). *)
load "preamble"; load "compilerTheory";
open HolKernel Parse bossLib preamble compilerTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "pancake_backend_conf_def_statement="; print_term (concl pancake_backend_conf_def); print "\n");
val _ = (print "pancake_backend_conf_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl pancake_backend_conf_def); print "\n");
val _ = print ("pancake_backend_conf_def_hypotheses=" ^ Int.toString (length (hyp pancake_backend_conf_def)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
