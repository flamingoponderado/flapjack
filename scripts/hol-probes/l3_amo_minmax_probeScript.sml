load "riscvTheory"; load "wordsLib"; load "state_transformerTheory";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "amomin_w_definition" dfn'AMOMIN_W_def;
val _ = (print "amomin_w_type=";print_type(type_of ``riscv$dfn'AMOMIN_W``);print "\n");
val _ = definition "amomin_d_definition" dfn'AMOMIN_D_def;
val _ = (print "amomin_d_type=";print_type(type_of ``riscv$dfn'AMOMIN_D``);print "\n");
val _ = definition "amomax_w_definition" dfn'AMOMAX_W_def;
val _ = (print "amomax_w_type=";print_type(type_of ``riscv$dfn'AMOMAX_W``);print "\n");
val _ = definition "amomax_d_definition" dfn'AMOMAX_D_def;
val _ = (print "amomax_d_type=";print_type(type_of ``riscv$dfn'AMOMAX_D``);print "\n");
val _ = definition "amominu_w_definition" dfn'AMOMINU_W_def;
val _ = (print "amominu_w_type=";print_type(type_of ``riscv$dfn'AMOMINU_W``);print "\n");
val _ = definition "amominu_d_definition" dfn'AMOMINU_D_def;
val _ = (print "amominu_d_type=";print_type(type_of ``riscv$dfn'AMOMINU_D``);print "\n");
val _ = definition "amomaxu_w_definition" dfn'AMOMAXU_W_def;
val _ = (print "amomaxu_w_type=";print_type(type_of ``riscv$dfn'AMOMAXU_W``);print "\n");
val _ = definition "amomaxu_d_definition" dfn'AMOMAXU_D_def;
val _ = (print "amomaxu_d_type=";print_type(type_of ``riscv$dfn'AMOMAXU_D``);print "\n");
val _ = computeLib.add_funs [dfn'AMOMIN_W_def,dfn'AMOMIN_D_def,dfn'AMOMAX_W_def,dfn'AMOMAX_D_def,dfn'AMOMINU_W_def,dfn'AMOMINU_D_def,dfn'AMOMAXU_W_def,dfn'AMOMAXU_D_def,dfn'AMOADD_W_def,dfn'AMOADD_D_def,dfn'AMOXOR_W_def,dfn'AMOXOR_D_def,dfn'AMOAND_W_def,dfn'AMOAND_D_def,dfn'AMOOR_W_def,dfn'AMOOR_D_def,dfn'AMOSWAP_W_def,dfn'AMOSWAP_D_def,dfn'SW_def,dfn'SH_def,dfn'SB_def,dfn'SD_def,dfn'SC_W_def,matchLoadReservation_def,ReserveLoad_def,write'ReserveLoad_def,dfn'LW_def,dfn'LWU_def,dfn'LH_def,dfn'LHU_def,dfn'LB_def,dfn'LBU_def,dfn'LD_def,gpr_def,GPR_def,write'gpr_def,write'GPR_def,signalAddressException_def,signalException_def,setTrap_def,write'NextFetch_def,architecture_def,curArch_def,in32BitMode_def,translateAddr_def,vmType_def,privilege_def,MCSR_def,TLBEntry_fn_updates,SV_PTE_fn_updates,translate64_def,curASID_def,ASID_SIZE_def,SCSR_def,TLB_def,write'TLB_def,addToTLB_def,mkTLBEntry_def,lookupTLB_def,FOR_def,walk64_def,rawReadData_def,rawWriteData_def,MEM_def,write'MEM_def,rec'SV_Vaddr_def,rec'SV_PTE_def,reg'SV_PTE_def,checkMemPermission_def,isGlobal_def,LEVEL_BITS_def,PAGESIZE_BITS_def,TLBEntries_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "amomin_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_misaligned_4_rd3" ``let c=7w:word8; a=4w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_misaligned_5_rd3" ``let c=7w:word8; a=5w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 5w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_misaligned_6_rd3" ``let c=7w:word8; a=6w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 6w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_misaligned_7_rd3" ``let c=7w:word8; a=7w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 7w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_both_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_equal_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 17w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(17 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_old_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(2147483648 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_source_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 9223372036854775808w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_old_signed_max_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(2147483647 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_w_source_upper32_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 4294967296w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_both_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_equal_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 17w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(17 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_old_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(9223372036854775808 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_source_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 9223372036854775808w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_old_signed_max_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(9223372036854775807 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomin_d_source_upper32_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 4294967296w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMIN_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_misaligned_4_rd3" ``let c=7w:word8; a=4w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_misaligned_5_rd3" ``let c=7w:word8; a=5w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 5w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_misaligned_6_rd3" ``let c=7w:word8; a=6w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 6w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_misaligned_7_rd3" ``let c=7w:word8; a=7w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 7w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_both_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_equal_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 17w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(17 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_old_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(2147483648 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_source_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 9223372036854775808w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_old_signed_max_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(2147483647 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_w_source_upper32_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 4294967296w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_both_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_equal_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 17w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(17 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_old_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(9223372036854775808 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_source_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 9223372036854775808w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_old_signed_max_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(9223372036854775807 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomax_d_source_upper32_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 4294967296w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAX_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_misaligned_4_rd3" ``let c=7w:word8; a=4w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_misaligned_5_rd3" ``let c=7w:word8; a=5w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 5w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_misaligned_6_rd3" ``let c=7w:word8; a=6w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 6w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_misaligned_7_rd3" ``let c=7w:word8; a=7w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 7w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_both_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_equal_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 17w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(17 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_old_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(2147483648 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_source_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 9223372036854775808w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_old_signed_max_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(2147483647 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_w_source_upper32_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 4294967296w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_both_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_equal_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 17w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(17 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_old_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(9223372036854775808 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_source_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 9223372036854775808w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_old_signed_max_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(9223372036854775807 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amominu_d_source_upper32_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 4294967296w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMINU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_misaligned_4_rd3" ``let c=7w:word8; a=4w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_misaligned_5_rd3" ``let c=7w:word8; a=5w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 5w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_misaligned_6_rd3" ``let c=7w:word8; a=6w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 6w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_misaligned_7_rd3" ``let c=7w:word8; a=7w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 7w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_both_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_equal_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 17w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(17 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_old_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(2147483648 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_source_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 9223372036854775808w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_old_signed_max_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(2147483647 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_w_source_upper32_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 4294967296w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_both_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_equal_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 17w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(17 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_old_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 0w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(9223372036854775808 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_source_signed_min_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 9223372036854775808w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_old_signed_max_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(9223372036854775807 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amomaxu_d_source_upper32_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 4294967296w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOMAXU_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
