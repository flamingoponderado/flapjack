(* Full original native encoder theorem specialized only to the complete Call constructor. *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val longdiv_case = GEN_ALL (Q.SPECL [`s1`, `Inst (Arith (LongDiv r1 r2 r3 r4 r5))`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_longdiv_statement="; print_term (concl longdiv_case); print "\n");
val _ = print ("riscv_encoder_correct_longdiv_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl longdiv_case)))) ^ "\n");
val _ = print ("riscv_encoder_correct_longdiv_hypotheses=" ^ Int.toString (length (hyp longdiv_case)) ^ "\n");
val _ = (print "riscv_encoder_correct_longdiv_proved="; print_term (rhs (concl (EQT_INTRO longdiv_case))); print "\n");
val fp_case = GEN_ALL (Q.SPECL [`s1`, `Inst (FP f)`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_fp_statement="; print_term (concl fp_case); print "\n");
val _ = print ("riscv_encoder_correct_fp_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl fp_case)))) ^ "\n");
val _ = print ("riscv_encoder_correct_fp_hypotheses=" ^ Int.toString (length (hyp fp_case)) ^ "\n");
val _ = (print "riscv_encoder_correct_fp_proved="; print_term (rhs (concl (EQT_INTRO fp_case))); print "\n");
val _ = OS.Process.exit OS.Process.success;
