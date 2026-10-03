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
val encode_rwts =
   let
      open riscvTheory
   in
      [riscv_enc_def, riscv_ast_def, riscv_encode_def, riscv_const32_def,
       riscv_bop_r_def, riscv_bop_i_def, riscv_sh_def, riscv_shv_def,
       riscv_memop_def, Encode_def, opc_def, Itype_def, Rtype_def, Stype_def,
       SBtype_def, Utype_def, UJtype_def]
   end;
val enc_ok_rwts =
  [asmPropsTheory.enc_ok_def, riscv_config, riscv_asm_ok] @ encode_rwts;
val riscv_target_ok = prove (``target_ok riscv_target``,
  rw ([asmPropsTheory.target_ok_def, asmPropsTheory.target_state_rel_def,
        riscv_proj_def, riscv_target_def, riscv_config, riscv_ok_def,
        set_sepTheory.fun2set_eq, riscv_encoding] @ enc_ok_rwts)
   >| [Cases_on `-0x100000w <= w1 /\ w1 <= 0xFFFFFw`
       \\ Cases_on `-0x100000w <= w2 /\ w2 <= 0xFFFFFw`,
       Cases_on `-0xFFCw <= w1 /\ w1 <= 0xFFFw`
       \\ Cases_on `-0xFFCw <= w2 /\ w2 <= 0xFFFw`
       \\ Cases_on `ri`
       \\ Cases_on `cmp`,
       Cases_on `-0x100000w <= w1 /\ w1 <= 0xFFFFFw`
       \\ Cases_on `-0x100000w <= w2 /\ w2 <= 0xFFFFFw`,
       all_tac
   ]
   \\ full_simp_tac (srw_ss()++boolSimps.LET_ss)
         (asmPropsTheory.offset_monotonic_def :: enc_ok_rwts)
   \\ DISCH_THEN kall_tac
   \\ blastLib.FULL_BBLAST_TAC);
val _ = (print "riscv_target_ok_statement="; print_term (concl riscv_target_ok); print "\n");
val _ = print ("riscv_target_ok_types=" ^ type_to_string (type_of ``riscv_target``) ^ "\n");
val _ = print ("riscv_target_ok_hypotheses=" ^ Int.toString (length (hyp riscv_target_ok)) ^ "\n");
val _ = (print "riscv_target_ok_proved="; print_term (rhs (concl (EQT_INTRO riscv_target_ok))); print "\n");
val _ = OS.Process.exit OS.Process.success;
