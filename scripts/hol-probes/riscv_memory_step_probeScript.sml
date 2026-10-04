load "preamble"; load "riscv_targetTheory"; load "riscv_stepTheory"; load "bitstringLib";
open HolKernel Parse bossLib preamble riscvTheory riscv_targetTheory asmTheory riscv_stepTheory;
val _ = Globals.linewidth := 1000000;
val _ = computeLib.add_funs [Run_def,gpr_def,GPR_def,write'gpr_def,write'GPR_def,
 dfn'LD_def,dfn'LWU_def,dfn'LHU_def,dfn'LBU_def,
 dfn'SD_def,dfn'SW_def,dfn'SH_def,dfn'SB_def,
 boolify8_def,boolify32_def,asSImm12_def,Encode_def,Itype_def,Stype_def,opc_def,Fetch_def,DecodeAny_def,Decode_def,NextRISCV_def,update_pc_def,PC_def,Skip_def,NextFetch_def,rawReadInst_def,write'Skip_def,write'PC_def,
 in32BitMode_def,curArch_def,architecture_def,MCSR_def,
 translateAddr_def,vmType_def,rawReadData_def,rawWriteData_def,MEM_def,write'MEM_def];
fun out label tm = let
 val th = (EVAL THENC SIMP_CONV (srw_ss()) [riscv_state_fn_updates] THENC EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV THENC EVAL) tm
 val result = rhs(concl th)
 in if null(hyp th) andalso aconv result ``T`` then
   (print(label ^ "="); print_term result; print "\n")
 else (print_term result; print "\n"; raise Fail ("non-true original memory Run observation: " ^ label)) end;
val _ = out "ld_next_sign" ``let i = Load (riscv$LD (5w,6w,2048w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "ld_next_zero" ``let i = Load (riscv$LD (0w,0w,4095w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "lwu_next_sign" ``let i = Load (riscv$LWU (5w,6w,2048w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "lwu_next_zero" ``let i = Load (riscv$LWU (0w,0w,4095w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "lhu_next_sign" ``let i = Load (riscv$LHU (5w,6w,2048w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "lhu_next_zero" ``let i = Load (riscv$LHU (0w,0w,4095w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "lbu_next_sign" ``let i = Load (riscv$LBU (5w,6w,2048w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "lbu_next_zero" ``let i = Load (riscv$LBU (0w,0w,4095w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "sd_next_sign" ``let i = Store (riscv$SD (5w,6w,2048w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "sd_next_zero" ``let i = Store (riscv$SD (0w,0w,4095w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "sw_next_sign" ``let i = Store (riscv$SW (5w,6w,2048w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "sw_next_zero" ``let i = Store (riscv$SW (0w,0w,4095w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "sh_next_sign" ``let i = Store (riscv$SH (5w,6w,2048w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "sh_next_zero" ``let i = Store (riscv$SH (0w,0w,4095w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "sb_next_sign" ``let i = Store (riscv$SB (5w,6w,2048w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val _ = out "sb_next_zero" ``let i = Store (riscv$SB (0w,0w,4095w)) in let w = Encode i in let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. 99w); MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
  mstatus := ((ARB:mstatus) with VM := 0w);
  mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in let fetched = write'Skip 4w s in let post = riscv$Run i fetched in riscv_step$NextRISCV s = SOME (write'PC 4w post)``;
val term = ``riscv_step$NextRISCV (ms:riscv_state)``;
val source = SIMP_CONV (srw_ss()) [NextRISCV_def] term;
val _ = (print "next_source_clause="; print_term(concl source); print "\n");
val _ = (print "next_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "next_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val term = ``riscv_step$update_pc (v:word64) (ms:riscv_state)``;
val source = SIMP_CONV (srw_ss()) [update_pc_def] term;
val _ = (print "pc_source_clause="; print_term(concl source); print "\n");
val _ = (print "pc_source_hypotheses="; print (Int.toString(length(hyp source)) ^ "\n"));
val _ = (print "pc_carrier_types="; print (String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (free_vars term)) ^ "\n"));
val _ = OS.Process.exit OS.Process.success;
