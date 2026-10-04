val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.linewidth := 1000000;
val slti_nop_full = GEN_ALL (DISCH_ALL SLTI_NOP);
val _ = (print "slti_nop_statement="; print_term(concl slti_nop_full); print "\n");
val _ = print ("slti_nop_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (#1(strip_forall(concl slti_nop_full)))) ^ "\n");
val _ = print ("slti_nop_source_hypotheses=" ^ Int.toString(length(hyp SLTI_NOP)) ^ "\n");
val _ = (print "slti_nop_proved="; print_term(rhs(concl(EQT_INTRO slti_nop_full))); print "\n");
val sltiu_nop_full = GEN_ALL (DISCH_ALL SLTIU_NOP);
val _ = (print "sltiu_nop_statement="; print_term(concl sltiu_nop_full); print "\n");
val _ = print ("sltiu_nop_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (#1(strip_forall(concl sltiu_nop_full)))) ^ "\n");
val _ = print ("sltiu_nop_source_hypotheses=" ^ Int.toString(length(hyp SLTIU_NOP)) ^ "\n");
val _ = (print "sltiu_nop_proved="; print_term(rhs(concl(EQT_INTRO sltiu_nop_full))); print "\n");
val _ = OS.Process.exit OS.Process.success;
