load "riscvTheory"; load "wordsLib"; load "state_transformerTheory";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "scw_definition" dfn'SC_W_def;
val _ = (print "scw_type=";print_type(type_of ``riscv$dfn'SC_W``);print "\n");
val _ = computeLib.add_funs [dfn'SC_W_def,matchLoadReservation_def,ReserveLoad_def,write'ReserveLoad_def,dfn'LW_def,dfn'LWU_def,dfn'LH_def,dfn'LHU_def,dfn'LB_def,dfn'LBU_def,dfn'LD_def,gpr_def,GPR_def,write'gpr_def,write'GPR_def,signalAddressException_def,signalException_def,setTrap_def,write'NextFetch_def,architecture_def,curArch_def,in32BitMode_def,translateAddr_def,vmType_def,privilege_def,MCSR_def,TLBEntry_fn_updates,SV_PTE_fn_updates,translate64_def,curASID_def,ASID_SIZE_def,SCSR_def,TLB_def,write'TLB_def,addToTLB_def,mkTLBEntry_def,lookupTLB_def,FOR_def,walk64_def,rawReadData_def,rawWriteData_def,MEM_def,write'MEM_def,rec'SV_Vaddr_def,rec'SV_PTE_def,reg'SV_PTE_def,checkMemPermission_def,isGlobal_def,LEVEL_BITS_def,PAGESIZE_BITS_def,TLBEntries_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "scw_negative" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_positive" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_rd_zero" ``let c=7w:word8; a=0w:word64; rd=0w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_core_wrap" ``let c=255w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_fault_sv32" ``let c=7w:word8; a=8w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_rv32_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_rv128_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_walk_returned_state" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_misaligned_1" ``let c=7w:word8; a=1w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_misaligned_2" ``let c=7w:word8; a=2w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_misaligned_3" ``let c=7w:word8; a=3w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_order_0_1" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,1w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_order_1_0" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (1w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_order_1_1" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (1w,1w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_reservation_mismatch" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=31w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME 21w else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_reservation_none" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=31w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then NONE else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_read_only_page" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_rs2_zero" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
val _ = out "scw_address_four" ``let c=7w:word8; a=4w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 3735928559w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);c_ReserveLoad:=(\id. if id=c then SOME a else SOME 21w);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'SC_W (0w,0w,rd,2w,3w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception;c_ReserveLoad:=s.c_ReserveLoad|>)=s,r.totalCore,w2n r.procID,OPTION_MAP w2n(ReserveLoad r),OPTION_MAP w2n(r.c_ReserveLoad(c+1w)))``;
OS.Process.exit OS.Process.success;
