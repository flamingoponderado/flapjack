(* Full original native encoder theorem specialized only to Inst Skip. *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val skip = GEN_ALL (Q.SPECL [`s1`, `Inst Skip`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_skip_statement="; print_term (concl skip); print "\n");
val _ = print ("riscv_encoder_correct_skip_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl skip)))) ^ "\n");
val _ = print ("riscv_encoder_correct_skip_hypotheses=" ^ Int.toString (length (hyp skip)) ^ "\n");
val _ = (print "riscv_encoder_correct_skip_proved="; print_term (rhs (concl (EQT_INTRO skip))); print "\n");
val _ = OS.Process.exit OS.Process.success;
