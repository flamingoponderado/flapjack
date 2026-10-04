(* Full original native riscv_target configuration and asm_ok rewrite bundles. *)
load "preamble"; load "riscv_targetTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val cfg = DB.fetch "riscv_target" "riscv_config";
val _ = (print "riscv_config_statement="; print_term (concl cfg); print "\n");
val _ = print ("riscv_config_hypotheses=" ^ Int.toString (length (hyp cfg)) ^ "\n");
val ok = DB.fetch "riscv_target" "riscv_asm_ok";
val _ = (print "riscv_asm_ok_statement="; print_term (concl ok); print "\n");
val _ = print ("riscv_asm_ok_hypotheses=" ^ Int.toString (length (hyp ok)) ^ "\n");
val _ = print "source=HOL riscv_targetScript.sml:331/333 asmLib.target_asm_rwts [] ``riscv_config`` generates riscv_config (config field bundle) and riscv_asm_ok (per-form asm_ok expansion); hypotheses=0 for both\n";
val _ = OS.Process.exit OS.Process.success;
