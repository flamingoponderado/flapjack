val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "preamble"; load "riscv_stepTheory"; load "bitstringLib";
open HolKernel Parse bossLib preamble riscvTheory riscv_stepTheory;
val _ = Globals.linewidth := 1000000;
val _ = computeLib.add_funs [Run_def, gpr_def, GPR_def,
 dfn'BEQ_def,dfn'BNE_def,dfn'BLT_def,dfn'BLTU_def,dfn'BGE_def,dfn'BGEU_def,
 branchTo_def,write'NextFetch_def,Encode_def,SBtype_def,opc_def,
 Fetch_def,DecodeAny_def,Decode_def,boolify8_def,boolify32_def,asImm12_def,
 NextRISCV_def,update_pc_def,PC_def,Skip_def,NextFetch_def,rawReadInst_def,
 write'Skip_def,write'PC_def,in32BitMode_def,curArch_def,architecture_def,MCSR_def,
 translateAddr_def,vmType_def];
val update_constant = Q.prove (`!a b. (a =+ b) (\x. b) = (\x. b)`,
  simp [combinTheory.UPDATE_def,FUN_EQ_THM]);
fun out label tm = let
 val th = (EVAL THENC SIMP_CONV (srw_ss()) [riscv_state_fn_updates,FUN_EQ_THM] THENC EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV THENC EVAL THENC SIMP_CONV (srw_ss()) [update_constant]) tm
 val result = rhs(concl th)
 in if null(hyp th) andalso aconv result ``T`` then
   (print(label ^ "="); print_term result; print "\n")
 else (print_term result; print "\n"; raise Fail ("non-true original memory Run observation: " ^ label)) end;
val _ = out "beq_next_zero" ``let i = Branch (BEQ (0w,0w,0w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 0w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 0w (write'Skip 4w s))``;
val _ = out "beq_next_alias_sign" ``let i = Branch (BEQ (31w,31w,2048w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 31w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 18446744073709547520w (write'Skip 4w s))``;
val _ = out "beq_next_odd_taken" ``let i = Branch (BEQ (1w,2w,4095w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 0w else 1w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "beq_next_odd_reverse" ``let i = Branch (BEQ (1w,2w,1w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 1w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "beq_next_signed_boundary" ``let i = Branch (BEQ (1w,2w,2047w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 9223372036854775808w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bne_next_zero" ``let i = Branch (BNE (0w,0w,0w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 0w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bne_next_alias_sign" ``let i = Branch (BNE (31w,31w,2048w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 31w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bne_next_odd_taken" ``let i = Branch (BNE (1w,2w,4095w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 0w else 1w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 18446744073709551614w (write'Skip 4w s))``;
val _ = out "bne_next_odd_reverse" ``let i = Branch (BNE (1w,2w,1w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 1w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 2w (write'Skip 4w s))``;
val _ = out "bne_next_signed_boundary" ``let i = Branch (BNE (1w,2w,2047w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 9223372036854775808w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4094w (write'Skip 4w s))``;
val _ = out "blt_next_zero" ``let i = Branch (BLT (0w,0w,0w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 0w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "blt_next_alias_sign" ``let i = Branch (BLT (31w,31w,2048w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 31w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "blt_next_odd_taken" ``let i = Branch (BLT (1w,2w,4095w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 0w else 1w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 18446744073709551614w (write'Skip 4w s))``;
val _ = out "blt_next_odd_reverse" ``let i = Branch (BLT (1w,2w,1w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 1w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "blt_next_signed_boundary" ``let i = Branch (BLT (1w,2w,2047w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 9223372036854775808w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4094w (write'Skip 4w s))``;
val _ = out "bltu_next_zero" ``let i = Branch (BLTU (0w,0w,0w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 0w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bltu_next_alias_sign" ``let i = Branch (BLTU (31w,31w,2048w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 31w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bltu_next_odd_taken" ``let i = Branch (BLTU (1w,2w,4095w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 0w else 1w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 18446744073709551614w (write'Skip 4w s))``;
val _ = out "bltu_next_odd_reverse" ``let i = Branch (BLTU (1w,2w,1w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 1w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bltu_next_signed_boundary" ``let i = Branch (BLTU (1w,2w,2047w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 9223372036854775808w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bge_next_zero" ``let i = Branch (BGE (0w,0w,0w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 0w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 0w (write'Skip 4w s))``;
val _ = out "bge_next_alias_sign" ``let i = Branch (BGE (31w,31w,2048w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 31w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 18446744073709547520w (write'Skip 4w s))``;
val _ = out "bge_next_odd_taken" ``let i = Branch (BGE (1w,2w,4095w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 0w else 1w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bge_next_odd_reverse" ``let i = Branch (BGE (1w,2w,1w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 1w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 2w (write'Skip 4w s))``;
val _ = out "bge_next_signed_boundary" ``let i = Branch (BGE (1w,2w,2047w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 9223372036854775808w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bgeu_next_zero" ``let i = Branch (BGEU (0w,0w,0w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 0w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 0w (write'Skip 4w s))``;
val _ = out "bgeu_next_alias_sign" ``let i = Branch (BGEU (31w,31w,2048w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 31w then 99w else 99w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 18446744073709547520w (write'Skip 4w s))``;
val _ = out "bgeu_next_odd_taken" ``let i = Branch (BGEU (1w,2w,4095w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 0w else 1w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4w (write'Skip 4w s))``;
val _ = out "bgeu_next_odd_reverse" ``let i = Branch (BGEU (1w,2w,1w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 1w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 2w (write'Skip 4w s))``;
val _ = out "bgeu_next_signed_boundary" ``let i = Branch (BGEU (1w,2w,2047w)) in let w = Encode i in
 let s = (ARB:riscv_state) with <| procID := 0w;
 c_gpr := (\core reg. if reg = 1w then 9223372036854775808w else 0w);
 MEM8 := (\addr. if addr = 0w then (7 >< 0) w else if addr = 1w then (15 >< 8) w else if addr = 2w then (23 >< 16) w else if addr = 3w then (31 >< 24) w else 165w);
 c_PC := (\core. 0w); c_NextFetch := (\core. NONE); exception := NoException;
 c_MCSR := (\core. (ARB:MachineCSR) with <|
 mstatus := ((ARB:mstatus) with VM := 0w);
 mcpuid := ((ARB:mcpuid) with ArchBase := 2w) |>) |> in
 NextRISCV s = SOME (write'PC 4094w (write'Skip 4w s))``;
val _ = (print "beq_source="; print_term (concl dfn'BEQ_def); print "\n");
val _ = print ("beq_hypotheses=" ^ Int.toString (length (hyp dfn'BEQ_def)) ^ "\n");
val _ = Globals.show_types := true;
val _ = (print "beq_typed_source="; print_term (concl dfn'BEQ_def); print "\n");
val _ = Globals.show_types := false;
val _ = (print "bne_source="; print_term (concl dfn'BNE_def); print "\n");
val _ = print ("bne_hypotheses=" ^ Int.toString (length (hyp dfn'BNE_def)) ^ "\n");
val _ = Globals.show_types := true;
val _ = (print "bne_typed_source="; print_term (concl dfn'BNE_def); print "\n");
val _ = Globals.show_types := false;
val _ = (print "blt_source="; print_term (concl dfn'BLT_def); print "\n");
val _ = print ("blt_hypotheses=" ^ Int.toString (length (hyp dfn'BLT_def)) ^ "\n");
val _ = Globals.show_types := true;
val _ = (print "blt_typed_source="; print_term (concl dfn'BLT_def); print "\n");
val _ = Globals.show_types := false;
val _ = (print "bltu_source="; print_term (concl dfn'BLTU_def); print "\n");
val _ = print ("bltu_hypotheses=" ^ Int.toString (length (hyp dfn'BLTU_def)) ^ "\n");
val _ = Globals.show_types := true;
val _ = (print "bltu_typed_source="; print_term (concl dfn'BLTU_def); print "\n");
val _ = Globals.show_types := false;
val _ = (print "bge_source="; print_term (concl dfn'BGE_def); print "\n");
val _ = print ("bge_hypotheses=" ^ Int.toString (length (hyp dfn'BGE_def)) ^ "\n");
val _ = Globals.show_types := true;
val _ = (print "bge_typed_source="; print_term (concl dfn'BGE_def); print "\n");
val _ = Globals.show_types := false;
val _ = (print "bgeu_source="; print_term (concl dfn'BGEU_def); print "\n");
val _ = print ("bgeu_hypotheses=" ^ Int.toString (length (hyp dfn'BGEU_def)) ^ "\n");
val _ = Globals.show_types := true;
val _ = (print "bgeu_typed_source="; print_term (concl dfn'BGEU_def); print "\n");
val _ = Globals.show_types := false;
val _ = (print "next_source="; print_term (concl NextRISCV_def); print "\n");
val _ = print ("next_hypotheses=" ^ Int.toString (length (hyp NextRISCV_def)) ^ "\n");
val _ = Globals.show_types := true;
val _ = (print "next_typed_source="; print_term (concl NextRISCV_def); print "\n");
val _ = Globals.show_types := false;
