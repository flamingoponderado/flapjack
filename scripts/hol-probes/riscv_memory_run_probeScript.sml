load "preamble"; load "riscv_targetTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_targetTheory asmTheory;
val _ = Globals.linewidth := 1000000;
val _ = computeLib.add_funs [Run_def,gpr_def,GPR_def,write'gpr_def,write'GPR_def,
 dfn'LD_def,dfn'LWU_def,dfn'LHU_def,dfn'LBU_def,
 dfn'SD_def,dfn'SW_def,dfn'SH_def,dfn'SB_def,
 in32BitMode_def,curArch_def,architecture_def,MCSR_def,
 translateAddr_def,vmType_def,rawReadData_def,rawWriteData_def,MEM_def,write'MEM_def];
fun out label tm = let
 val th = (EVAL THENC SIMP_CONV (srw_ss()) [riscv_state_fn_updates] THENC EVAL) tm
 val result = rhs(concl th)
 in if null(hyp th) andalso aconv result ``T`` then
   (print(label ^ "="); print_term result; print "\n")
 else (print_term result; print "\n"; raise Fail ("non-true original memory Run observation: " ^ label)) end;
val _ = out "ld_run_zero" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LD (0w,0w,4095w))) s in r = s``;
val _ = out "ld_run_alias_sign" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LD (5w,5w,2048w))) s in GPR 5w r = 11936128518282651045w /\ GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\ (r with c_gpr := s.c_gpr) = s``;
val _ = out "ld_run_basezero_unaligned" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LD (5w,0w,1w))) s in GPR 5w r = 11936128518282651045w /\ GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\ (r with c_gpr := s.c_gpr) = s``;
val _ = out "lwu_run_zero" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LWU (0w,0w,4095w))) s in r = s``;
val _ = out "lwu_run_alias_sign" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LWU (5w,5w,2048w))) s in GPR 5w r = 2779096485w /\ GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\ (r with c_gpr := s.c_gpr) = s``;
val _ = out "lwu_run_basezero_unaligned" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LWU (5w,0w,1w))) s in GPR 5w r = 2779096485w /\ GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\ (r with c_gpr := s.c_gpr) = s``;
val _ = out "lhu_run_zero" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LHU (0w,0w,4095w))) s in r = s``;
val _ = out "lhu_run_alias_sign" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LHU (5w,5w,2048w))) s in GPR 5w r = 42405w /\ GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\ (r with c_gpr := s.c_gpr) = s``;
val _ = out "lhu_run_basezero_unaligned" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LHU (5w,0w,1w))) s in GPR 5w r = 42405w /\ GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\ (r with c_gpr := s.c_gpr) = s``;
val _ = out "lbu_run_zero" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LBU (0w,0w,4095w))) s in r = s``;
val _ = out "lbu_run_alias_sign" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LBU (5w,5w,2048w))) s in GPR 5w r = 165w /\ GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\ (r with c_gpr := s.c_gpr) = s``;
val _ = out "lbu_run_basezero_unaligned" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Load (riscv$LBU (5w,0w,1w))) s in GPR 5w r = 165w /\ GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\ (r with c_gpr := s.c_gpr) = s``;
val _ = out "sd_run_basezero_sign" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Store (riscv$SD (0w,5w,4095w))) s in r = rawWriteData ((-1w:word64),99w,8) s /\ (r with MEM8 := s.MEM8) = s``;
val _ = out "sd_run_alias" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Store (riscv$SD (5w,5w,1w))) s in r = rawWriteData (100w,99w,8) s /\ (r with MEM8 := s.MEM8) = s``;
val _ = out "sw_run_basezero_sign" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Store (riscv$SW (0w,5w,4095w))) s in r = rawWriteData ((-1w:word64),99w,4) s /\ (r with MEM8 := s.MEM8) = s``;
val _ = out "sw_run_alias" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Store (riscv$SW (5w,5w,1w))) s in r = rawWriteData (100w,99w,4) s /\ (r with MEM8 := s.MEM8) = s``;
val _ = out "sh_run_basezero_sign" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Store (riscv$SH (0w,5w,4095w))) s in r = rawWriteData ((-1w:word64),99w,2) s /\ (r with MEM8 := s.MEM8) = s``;
val _ = out "sh_run_alias" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Store (riscv$SH (5w,5w,1w))) s in r = rawWriteData (100w,99w,2) s /\ (r with MEM8 := s.MEM8) = s``;
val _ = out "sb_run_basezero_sign" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Store (riscv$SB (0w,5w,4095w))) s in r = rawWriteData ((-1w:word64),99w,1) s /\ (r with MEM8 := s.MEM8) = s``;
val _ = out "sb_run_alias" ``let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |>; r = riscv$Run (Store (riscv$SB (5w,5w,1w))) s in r = rawWriteData (100w,99w,1) s /\ (r with MEM8 := s.MEM8) = s``;
val term = ``riscv$Run (Load (riscv$LD (r1v,r2v,offs))) ms``;
val source = SIMP_CONV (srw_ss()) [Run_def] term;
val _ = (print "ld_run_source_clause="; (print_term(concl source); print "\n"));
val _ = (print "ld_run_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "ld_run_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val term = ``riscv$Run (Load (riscv$LWU (r1v,r2v,offs))) ms``;
val source = SIMP_CONV (srw_ss()) [Run_def] term;
val _ = (print "lwu_run_source_clause="; (print_term(concl source); print "\n"));
val _ = (print "lwu_run_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "lwu_run_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val term = ``riscv$Run (Load (riscv$LHU (r1v,r2v,offs))) ms``;
val source = SIMP_CONV (srw_ss()) [Run_def] term;
val _ = (print "lhu_run_source_clause="; (print_term(concl source); print "\n"));
val _ = (print "lhu_run_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "lhu_run_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val term = ``riscv$Run (Load (riscv$LBU (r1v,r2v,offs))) ms``;
val source = SIMP_CONV (srw_ss()) [Run_def] term;
val _ = (print "lbu_run_source_clause="; (print_term(concl source); print "\n"));
val _ = (print "lbu_run_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "lbu_run_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val term = ``riscv$Run (Store (riscv$SD (r1v,r2v,offs))) ms``;
val source = SIMP_CONV (srw_ss()) [Run_def] term;
val _ = (print "sd_run_source_clause="; (print_term(concl source); print "\n"));
val _ = (print "sd_run_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "sd_run_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val term = ``riscv$Run (Store (riscv$SW (r1v,r2v,offs))) ms``;
val source = SIMP_CONV (srw_ss()) [Run_def] term;
val _ = (print "sw_run_source_clause="; (print_term(concl source); print "\n"));
val _ = (print "sw_run_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "sw_run_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val term = ``riscv$Run (Store (riscv$SH (r1v,r2v,offs))) ms``;
val source = SIMP_CONV (srw_ss()) [Run_def] term;
val _ = (print "sh_run_source_clause="; (print_term(concl source); print "\n"));
val _ = (print "sh_run_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "sh_run_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val term = ``riscv$Run (Store (riscv$SB (r1v,r2v,offs))) ms``;
val source = SIMP_CONV (srw_ss()) [Run_def] term;
val _ = (print "sb_run_source_clause="; (print_term(concl source); print "\n"));
val _ = (print "sb_run_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "sb_run_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val _ = OS.Process.exit OS.Process.success;
