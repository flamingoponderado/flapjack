(* Full original native encoder theorem specialized only to the complete Jump constructor. *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val jump_case = GEN_ALL (Q.SPECL [`s1`, `Jump c`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_jump_statement="; print_term (concl jump_case); print "\n");
val _ = print ("riscv_encoder_correct_jump_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl jump_case)))) ^ "\n");
val _ = print ("riscv_encoder_correct_jump_hypotheses=" ^ Int.toString (length (hyp jump_case)) ^ "\n");
val _ = (print "riscv_encoder_correct_jump_proved="; print_term (rhs (concl (EQT_INTRO jump_case))); print "\n");
val _ = OS.Process.exit OS.Process.success;
