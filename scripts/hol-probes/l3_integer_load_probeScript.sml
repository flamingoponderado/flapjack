load "riscvTheory"; load "wordsLib"; load "state_transformerTheory";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "lw_definition" dfn'LW_def;
val _ = (print "lw_type=";print_type(type_of ``riscv$dfn'LW``);print "\n");
val _ = definition "lwu_definition" dfn'LWU_def;
val _ = (print "lwu_type=";print_type(type_of ``riscv$dfn'LWU``);print "\n");
val _ = definition "lh_definition" dfn'LH_def;
val _ = (print "lh_type=";print_type(type_of ``riscv$dfn'LH``);print "\n");
val _ = definition "lhu_definition" dfn'LHU_def;
val _ = (print "lhu_type=";print_type(type_of ``riscv$dfn'LHU``);print "\n");
val _ = definition "lb_definition" dfn'LB_def;
val _ = (print "lb_type=";print_type(type_of ``riscv$dfn'LB``);print "\n");
val _ = definition "lbu_definition" dfn'LBU_def;
val _ = (print "lbu_type=";print_type(type_of ``riscv$dfn'LBU``);print "\n");
val _ = definition "ld_definition" dfn'LD_def;
val _ = (print "ld_type=";print_type(type_of ``riscv$dfn'LD``);print "\n");
val _ = computeLib.add_funs [dfn'LW_def,dfn'LWU_def,dfn'LH_def,dfn'LHU_def,dfn'LB_def,dfn'LBU_def,dfn'LD_def,gpr_def,GPR_def,write'gpr_def,write'GPR_def,signalAddressException_def,signalException_def,setTrap_def,write'NextFetch_def,architecture_def,curArch_def,in32BitMode_def,translateAddr_def,vmType_def,privilege_def,MCSR_def,TLBEntry_fn_updates,SV_PTE_fn_updates,translate64_def,curASID_def,ASID_SIZE_def,SCSR_def,TLB_def,write'TLB_def,addToTLB_def,mkTLBEntry_def,lookupTLB_def,FOR_def,walk64_def,rawReadData_def,rawWriteData_def,MEM_def,write'MEM_def,rec'SV_Vaddr_def,rec'SV_PTE_def,reg'SV_PTE_def,checkMemPermission_def,isGlobal_def,LEVEL_BITS_def,PAGESIZE_BITS_def,TLBEntries_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "lw_negative" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_positive" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_rd_zero" ``let c=7w:word8; a=0w:word64; rd=0w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_unaligned" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_offset_wrap" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,1w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_core_wrap" ``let c=255w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_fault_sv32" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_rv32_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_rv128_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lw_walk_returned_state" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LW (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_negative" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_positive" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_rd_zero" ``let c=7w:word8; a=0w:word64; rd=0w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_unaligned" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_offset_wrap" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,1w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_core_wrap" ``let c=255w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_fault_sv32" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_rv32_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_rv128_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lwu_walk_returned_state" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LWU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_negative" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_positive" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_rd_zero" ``let c=7w:word8; a=0w:word64; rd=0w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_unaligned" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_offset_wrap" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,1w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_core_wrap" ``let c=255w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_fault_sv32" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_rv32_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_rv128_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lh_walk_returned_state" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LH (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_negative" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_positive" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_rd_zero" ``let c=7w:word8; a=0w:word64; rd=0w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_unaligned" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_offset_wrap" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,1w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_core_wrap" ``let c=255w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_fault_sv32" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_rv32_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_rv128_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lhu_walk_returned_state" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LHU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_negative" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_positive" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_rd_zero" ``let c=7w:word8; a=0w:word64; rd=0w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_unaligned" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_offset_wrap" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,1w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_core_wrap" ``let c=255w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_fault_sv32" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_rv32_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_rv128_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lb_walk_returned_state" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LB (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_negative" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_positive" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_rd_zero" ``let c=7w:word8; a=0w:word64; rd=0w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_unaligned" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_offset_wrap" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,1w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_core_wrap" ``let c=255w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_fault_sv32" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_rv32_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_rv128_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "lbu_walk_returned_state" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LBU (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_negative" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_positive" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_rd_zero" ``let c=7w:word8; a=0w:word64; rd=0w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_unaligned" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_offset_wrap" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,1w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_core_wrap" ``let c=255w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_fault_sv32" ``let c=7w:word8; a=7w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 8w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=8w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,4095w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_rv32_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_rv128_mode" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "ld_walk_returned_state" ``let c=7w:word8; a=0w:word64; rd=1w:word5;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'LD (rd,2w,0w) s in
 (w2n(GPR rd r),w2n(r.c_gpr c rd),w2n(r.c_gpr(c+1w) rd),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=Load_Fault then 1 else if t.trap=Illegal_Instr then 2 else 3,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(r.MEM8 a),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|MEM8:=s.MEM8;c_gpr:=s.c_gpr;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
OS.Process.exit OS.Process.success;
