(* Whole source behavior observations, derived in the original HOL kernel. *)
load "preamble";
load "labSemTheory";
open bossLib HolKernel Parse preamble labSemTheory;
fun show_goal (asl,w) =
  (TextIO.output (TextIO.stdErr, term_to_string w ^ "\n"); ALL_TAC (asl,w));
val nz_exists = prove (``?k:num. k <> 0``, qexists_tac `1` >> simp []);
val empty_eval = SIMP_CONV (srw_ss())
  [Once evaluate_def, asm_fetch_def, asm_fetch_aux_def]
  ``evaluate ((s:(64,num,num)labSem$state) with <|code:=[];pc:=0;clock:=k|>)``;
val halt0_eval = SIMP_CONV (srw_ss())
  [Once evaluate_def, asm_fetch_def, asm_fetch_aux_def]
  ``evaluate ((s:(64,num,num)labSem$state) with
    <|code:=[Section 1 [LabAsm Halt 0w [] 7]];pc:=0;ptr_reg:=0;regs:=(\r.Word 0w);clock:=k|>)``;
val halt1_eval = SIMP_CONV (srw_ss())
  [Once evaluate_def, asm_fetch_def, asm_fetch_aux_def]
  ``evaluate ((s:(64,num,num)labSem$state) with
    <|code:=[Section 1 [LabAsm Halt 0w [] 7]];pc:=0;ptr_reg:=0;regs:=(\r.Word 1w);clock:=k|>)``;
(* Induction covers every clock, rather than a finite timeout observation. *)
val loop_eval = prove (
  ``!k. evaluate ((s:(64,num,num)labSem$state) with
      <|code:=[Section 1 [LabAsm (Jump (Lab 1 0)) 0w [] 7]];pc:=0;clock:=k|>) =
      (TimeOut,s with <|code:=[Section 1 [LabAsm (Jump (Lab 1 0)) 0w [] 7]];pc:=0;clock:=0|>)``,
  Induct >> fs [] >> simp [Once evaluate_def, asm_fetch_def, asm_fetch_aux_def,
    get_pc_value_def, loc_to_pc_def, upd_pc_def, dec_clock_def] >> show_goal);
val _ = TextIO.output (TextIO.stdErr, "all-clock loop equation proved\n");
val singleton_lub = prove (``build_lprefix_lub {ll:'a llist} = ll``,
  match_mp_tac lprefix_lubTheory.unique_lprefix_lub >>
  qexists_tac `{ll}` >> conj_tac >-
    (match_mp_tac lprefix_lubTheory.build_lprefix_lub_thm >>
     simp [lprefix_lubTheory.lprefix_chain_def]) >>
  simp [lprefix_lubTheory.lprefix_lub_def] >> show_goal);
val _ = TextIO.output (TextIO.stdErr, "singleton LUB proved\n");
fun out label q =
  (print (label ^ "=");
   print_term (rconc (SIMP_CONV (srw_ss())
     [semantics_def,
      CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [])) empty_eval,
      CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [])) halt0_eval,
      CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [])) halt1_eval,
      CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [])) (SPEC_ALL loop_eval),
      singleton_lub, pred_setTheory.IMAGE_CONST,
      COND_RAND, COND_RATOR, AllCaseEqs(), LEFT_EXISTS_AND_THM, nz_exists] q)); print "\n");
val _ = out "lab_semantics_empty_error"
  ``labSem$semantics ((s:(64,num,num)labSem$state) with <|code:=[];pc:=0|>) = Fail``;
val _ = out "lab_semantics_halt_success"
  ``labSem$semantics ((s:(64,num,num)labSem$state) with
      <|code:=[Section 1 [LabAsm Halt 0w [] 7]];pc:=0;ptr_reg:=0;regs:=(\r.Word 0w)|>)
      = Terminate Success s.ffi.io_events``;
val _ = out "lab_semantics_halt_resource"
  ``labSem$semantics ((s:(64,num,num)labSem$state) with
      <|code:=[Section 1 [LabAsm Halt 0w [] 7]];pc:=0;ptr_reg:=0;regs:=(\r.Word 1w)|>)
      = Terminate Resource_limit_hit s.ffi.io_events``;
val _ = out "lab_semantics_loop_diverge"
  ``labSem$semantics ((s:(64,num,num)labSem$state) with
      <|code:=[Section 1 [LabAsm (Jump (Lab 1 0)) 0w [] 7]];pc:=0|>)
      = Diverge (fromList s.ffi.io_events)``;
val _ = OS.Process.exit OS.Process.success;
