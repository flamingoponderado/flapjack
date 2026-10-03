load "riscvTheory"; load "wordsLib"; load "state_transformerTheory";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "amoswap_w_definition" dfn'AMOSWAP_W_def;
val _ = (print "amoswap_w_type=";print_type(type_of ``riscv$dfn'AMOSWAP_W``);print "\n");
val _ = definition "amoswap_d_definition" dfn'AMOSWAP_D_def;
val _ = (print "amoswap_d_type=";print_type(type_of ``riscv$dfn'AMOSWAP_D``);print "\n");
val _ = computeLib.add_funs [dfn'AMOSWAP_W_def,dfn'AMOSWAP_D_def,dfn'SW_def,dfn'SH_def,dfn'SB_def,dfn'SD_def,dfn'SC_W_def,matchLoadReservation_def,ReserveLoad_def,write'ReserveLoad_def,dfn'LW_def,dfn'LWU_def,dfn'LH_def,dfn'LHU_def,dfn'LB_def,dfn'LBU_def,dfn'LD_def,gpr_def,GPR_def,write'gpr_def,write'GPR_def,signalAddressException_def,signalException_def,setTrap_def,write'NextFetch_def,architecture_def,curArch_def,in32BitMode_def,translateAddr_def,vmType_def,privilege_def,MCSR_def,TLBEntry_fn_updates,SV_PTE_fn_updates,translate64_def,curASID_def,ASID_SIZE_def,SCSR_def,TLB_def,write'TLB_def,addToTLB_def,mkTLBEntry_def,lookupTLB_def,FOR_def,walk64_def,rawReadData_def,rawWriteData_def,MEM_def,write'MEM_def,rec'SV_Vaddr_def,rec'SV_PTE_def,reg'SV_PTE_def,checkMemPermission_def,isGlobal_def,LEVEL_BITS_def,PAGESIZE_BITS_def,TLBEntries_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "amoswap_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoswap_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOSWAP_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
