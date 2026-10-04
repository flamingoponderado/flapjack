(* Complete generated per-form asm_ok theorem; no subset or new assumptions. *)
load "preamble"; load "riscv_targetTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val full = GEN_ALL riscv_asm_ok;
val (vars,body) = strip_forall (concl full);
val _ = (print "riscv_asm_ok_full_statement="; print_term (concl full); print "\n");
val _ = print ("riscv_asm_ok_full_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) vars) ^ "\n");
val _ = print ("riscv_asm_ok_full_conjuncts=" ^ Int.toString (length (strip_conj body)) ^ "\n");
val _ = print ("riscv_asm_ok_full_hypotheses=" ^ Int.toString (length (hyp full)) ^ "\n");
val _ = (print "riscv_asm_ok_full_proved="; print_term (rhs (concl (EQT_INTRO full))); print "\n");
val _ = OS.Process.exit OS.Process.success;
