load "riscvTheory"; load "wordsLib";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "architecture_definition" architecture_def;
val _ = (print "architecture_type=";print_type(type_of ``riscv$architecture``);print "\n");
val _ = definition "curArch_definition" curArch_def;
val _ = (print "curArch_type=";print_type(type_of ``riscv$curArch``);print "\n");
val _ = definition "in32BitMode_definition" in32BitMode_def;
val _ = (print "in32BitMode_type=";print_type(type_of ``riscv$in32BitMode``);print "\n");
val _ = computeLib.add_funs [architecture_def,curArch_def,in32BitMode_def,MCSR_def,raise'exception_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "selector_0" ``let s=((ARB:riscv_state) with <|procID:=255w;totalCore:=1;exception:=NoException;c_MCSR:=(\id. (ARB:MachineCSR) with mcpuid:=((ARB:mcpuid) with ArchBase:=0w))|>); a=curArch () s; b=in32BitMode () s in
 (FST a=RV32I,FST b=(RV32I=RV32I),SND a=SND b,(SND a).exception=(NoException),(SND b).procID=255w,(SND b).totalCore=1,(SND b).c_MCSR=s.c_MCSR)``;
val _ = out "selector_1" ``let s=((ARB:riscv_state) with <|procID:=255w;totalCore:=1;exception:=NoException;c_MCSR:=(\id. (ARB:MachineCSR) with mcpuid:=((ARB:mcpuid) with ArchBase:=1w))|>); a=curArch () s; b=in32BitMode () s in
 (FST a=(ARB:Architecture),FST b=((ARB:Architecture)=RV32I),SND a=SND b,(SND a).exception=(UNDEFINED "Unknown architecture: 1"),(SND b).procID=255w,(SND b).totalCore=1,(SND b).c_MCSR=s.c_MCSR)``;
val _ = out "selector_2" ``let s=((ARB:riscv_state) with <|procID:=255w;totalCore:=1;exception:=NoException;c_MCSR:=(\id. (ARB:MachineCSR) with mcpuid:=((ARB:mcpuid) with ArchBase:=2w))|>); a=curArch () s; b=in32BitMode () s in
 (FST a=RV64I,FST b=(RV64I=RV32I),SND a=SND b,(SND a).exception=(NoException),(SND b).procID=255w,(SND b).totalCore=1,(SND b).c_MCSR=s.c_MCSR)``;
val _ = out "selector_3" ``let s=((ARB:riscv_state) with <|procID:=255w;totalCore:=1;exception:=NoException;c_MCSR:=(\id. (ARB:MachineCSR) with mcpuid:=((ARB:mcpuid) with ArchBase:=3w))|>); a=curArch () s; b=in32BitMode () s in
 (FST a=RV128I,FST b=(RV128I=RV32I),SND a=SND b,(SND a).exception=(NoException),(SND b).procID=255w,(SND b).totalCore=1,(SND b).c_MCSR=s.c_MCSR)``;
OS.Process.exit OS.Process.success;
