(* Unconditional complete original theorem, plus its literal contract expansion. *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val full = riscv_encoder_correct;
val expanded = REWRITE_RULE [encoder_correct_def] full;
val _ = (print "riscv_encoder_correct_statement="; print_term (concl full); print "\n");
val _ = (print "riscv_encoder_correct_expanded="; print_term (concl expanded); print "\n");
val _ = print ("riscv_encoder_correct_hypotheses=" ^ Int.toString (length (hyp full)) ^ "\n");
val _ = (print "riscv_encoder_correct_proved="; print_term (rhs (concl (EQT_INTRO full))); print "\n");
val _ = OS.Process.exit OS.Process.success;
