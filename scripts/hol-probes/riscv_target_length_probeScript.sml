(* Full literal original universal native encoding contract proofs. *)
load "preamble"; load "riscv_targetTheory"; load "asmLib";
open HolKernel Parse bossLib preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;
val length_riscv_encode = prove (``!i. LENGTH (riscv_encode i) = 4``,
rw [riscv_encode_def]);
val riscv_encode_not_nil = prove (``!i. riscv_encode i <> []``,
simp_tac std_ss [length_riscv_encode, GSYM listTheory.LENGTH_NIL]);
val riscv_encoding = Q.prove (
   `!i. let l = riscv_enc i in (LENGTH l MOD 4 = 0) /\ l <> []`,
   strip_tac
   \\ asmLib.asm_cases_tac `i`
   \\ rw [riscv_enc_def, riscv_const32_def, riscv_encode_fail_def,
          length_riscv_encode, riscv_encode_not_nil, riscv_ast_def]
   \\ REPEAT CASE_TAC
   \\ rw [length_riscv_encode, riscv_encode_not_nil]
   )
   |> SIMP_RULE (srw_ss()++boolSimps.LET_ss) [riscv_enc_def];
val _ = (print "length_riscv_encode_statement="; print_term (concl (GEN_ALL length_riscv_encode)); print "\n");
val _ = print ("length_riscv_encode_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl (GEN_ALL length_riscv_encode))))) ^ "\n");
val _ = print ("length_riscv_encode_hypotheses=" ^ Int.toString (length (hyp length_riscv_encode)) ^ "\n");
val _ = (print "length_riscv_encode_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL length_riscv_encode)))); print "\n");
val _ = (print "riscv_encode_not_nil_statement="; print_term (concl (GEN_ALL riscv_encode_not_nil)); print "\n");
val _ = print ("riscv_encode_not_nil_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl (GEN_ALL riscv_encode_not_nil))))) ^ "\n");
val _ = print ("riscv_encode_not_nil_hypotheses=" ^ Int.toString (length (hyp riscv_encode_not_nil)) ^ "\n");
val _ = (print "riscv_encode_not_nil_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL riscv_encode_not_nil)))); print "\n");
val _ = (print "riscv_encoding_statement="; print_term (concl (GEN_ALL riscv_encoding)); print "\n");
val _ = print ("riscv_encoding_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl (GEN_ALL riscv_encoding))))) ^ "\n");
val _ = print ("riscv_encoding_hypotheses=" ^ Int.toString (length (hyp riscv_encoding)) ^ "\n");
val _ = (print "riscv_encoding_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL riscv_encoding)))); print "\n");
val _ = OS.Process.exit OS.Process.success;
