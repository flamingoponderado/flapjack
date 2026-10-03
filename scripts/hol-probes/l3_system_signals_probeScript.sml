load "riscvTheory"; load "wordsLib"; load "state_transformerTheory";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "signal0_definition" signalEnvCall_def;
val _ = (print "signal0_type=";print_type(type_of ``riscv$signalEnvCall``);print "\n");
val _ = definition "signal1_definition" dfn'ECALL_def;
val _ = (print "signal1_type=";print_type(type_of ``riscv$dfn'ECALL``);print "\n");
val _ = definition "signal2_definition" dfn'EBREAK_def;
val _ = (print "signal2_type=";print_type(type_of ``riscv$dfn'EBREAK``);print "\n");
val _ = definition "signal3_definition" dfn'ERET_def;
val _ = (print "signal3_type=";print_type(type_of ``riscv$dfn'ERET``);print "\n");
val _ = definition "signal4_definition" dfn'UnknownInstruction_def;
val _ = (print "signal4_type=";print_type(type_of ``riscv$dfn'UnknownInstruction``);print "\n");
val _ = computeLib.add_funs [signalEnvCall_def,dfn'ECALL_def,dfn'EBREAK_def,dfn'ERET_def,dfn'UnknownInstruction_def,signalException_def,setTrap_def,write'NextFetch_def,MCSR_def,privilege_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "signal0_priv0_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv0_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv0_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv0_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv1_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv1_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv1_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv1_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv2_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv2_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv2_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv2_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv3_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv3_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv3_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal0_priv3_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=signalEnvCall () s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv0_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv0_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv0_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv0_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv1_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv1_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv1_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv1_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv2_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv2_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv2_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv2_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv3_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv3_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv3_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal1_priv3_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'ECALL s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv0_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv0_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv0_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv0_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv1_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv1_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv1_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv1_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv2_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv2_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv2_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv2_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv3_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv3_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv3_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal2_priv3_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'EBREAK s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv0_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv0_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv0_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv0_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv1_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv1_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv1_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv1_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv2_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv2_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv2_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv2_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv3_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv3_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv3_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal3_priv3_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'ERET s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv0_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv0_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv0_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv0_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=0w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv1_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv1_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv1_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv1_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=1w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv2_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv2_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv2_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv2_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=2w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv3_prior0_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv3_prior0_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv3_prior1_core7" ``let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
val _ = out "signal4_priv3_prior1_core255" ``let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=INTERNAL_ERROR "existing";c_NextFetch:=(\id. SOME Ereturn);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with MPRV:=3w))|>);
 r=dfn'UnknownInstruction s in ((case r.c_NextFetch c of SOME (Trap t) =>
 ((if t.trap=Illegal_Instr then 1 else if t.trap=Breakpoint then 2 else if t.trap=UMode_Env_Call then 3 else if t.trap=SMode_Env_Call then 4 else if t.trap=HMode_Env_Call then 5 else if t.trap=MMode_Env_Call then 6 else 9),OPTION_MAP w2n t.badaddr)
 | SOME Ereturn => (7,NONE) | _ => (0,NONE)),r.c_NextFetch(c+1w)=SOME Ereturn,r.exception=s.exception,
 (r with c_NextFetch:=s.c_NextFetch)=s,r.totalCore,w2n r.procID)``;
