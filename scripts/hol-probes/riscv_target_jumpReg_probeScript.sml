(* Full original native encoder theorem specialized only to JumpReg r. *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val jumpReg = GEN_ALL (Q.SPECL [`s1`, `JumpReg r`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_jumpReg_statement="; print_term (concl jumpReg); print "\n");
val _ = print ("riscv_encoder_correct_jumpReg_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl jumpReg)))) ^ "\n");
val _ = print ("riscv_encoder_correct_jumpReg_hypotheses=" ^ Int.toString (length (hyp jumpReg)) ^ "\n");
val _ = (print "riscv_encoder_correct_jumpReg_proved="; print_term (rhs (concl (EQT_INTRO jumpReg))); print "\n");
val _ = OS.Process.exit OS.Process.success;
