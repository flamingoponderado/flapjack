(* Exported original-theory capture of riscv_configScript riscv_backend_config_def (56-70),
   with the antiquoted SML configuration values already spliced by HOL. *)
load "preamble"; load "riscv_configTheory";
open HolKernel Parse bossLib preamble riscv_configTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "riscv_backend_config_def_statement="; print_term (concl riscv_backend_config_def); print "\n");
val _ = (print "riscv_backend_config_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl riscv_backend_config_def); print "\n");
val _ = print ("riscv_backend_config_def_hypotheses=" ^ Int.toString (length (hyp riscv_backend_config_def)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
