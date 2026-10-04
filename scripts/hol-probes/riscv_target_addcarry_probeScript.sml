(* Full original native encoder theorem specialized only to the complete AddCarry constructor. *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val addcarry_case = GEN_ALL (Q.SPECL [`s1`, `Inst (Arith (AddCarry r1 r2 r3 r4))`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_addcarry_statement="; print_term (concl addcarry_case); print "\n");
val _ = print ("riscv_encoder_correct_addcarry_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl addcarry_case)))) ^ "\n");
val _ = print ("riscv_encoder_correct_addcarry_hypotheses=" ^ Int.toString (length (hyp addcarry_case)) ^ "\n");
val _ = (print "riscv_encoder_correct_addcarry_proved="; print_term (rhs (concl (EQT_INTRO addcarry_case))); print "\n");
val _ = OS.Process.exit OS.Process.success;
