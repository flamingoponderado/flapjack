load "riscvTheory"; load "wordsLib"; load "state_transformerTheory";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "amoadd_w_definition" dfn'AMOADD_W_def;
val _ = (print "amoadd_w_type=";print_type(type_of ``riscv$dfn'AMOADD_W``);print "\n");
val _ = definition "amoadd_d_definition" dfn'AMOADD_D_def;
val _ = (print "amoadd_d_type=";print_type(type_of ``riscv$dfn'AMOADD_D``);print "\n");
val _ = definition "amoxor_w_definition" dfn'AMOXOR_W_def;
val _ = (print "amoxor_w_type=";print_type(type_of ``riscv$dfn'AMOXOR_W``);print "\n");
val _ = definition "amoxor_d_definition" dfn'AMOXOR_D_def;
val _ = (print "amoxor_d_type=";print_type(type_of ``riscv$dfn'AMOXOR_D``);print "\n");
val _ = definition "amoand_w_definition" dfn'AMOAND_W_def;
val _ = (print "amoand_w_type=";print_type(type_of ``riscv$dfn'AMOAND_W``);print "\n");
val _ = definition "amoand_d_definition" dfn'AMOAND_D_def;
val _ = (print "amoand_d_type=";print_type(type_of ``riscv$dfn'AMOAND_D``);print "\n");
val _ = definition "amoor_w_definition" dfn'AMOOR_W_def;
val _ = (print "amoor_w_type=";print_type(type_of ``riscv$dfn'AMOOR_W``);print "\n");
val _ = definition "amoor_d_definition" dfn'AMOOR_D_def;
val _ = (print "amoor_d_type=";print_type(type_of ``riscv$dfn'AMOOR_D``);print "\n");
val _ = computeLib.add_funs [dfn'AMOADD_W_def,dfn'AMOADD_D_def,dfn'AMOXOR_W_def,dfn'AMOXOR_D_def,dfn'AMOAND_W_def,dfn'AMOAND_D_def,dfn'AMOOR_W_def,dfn'AMOOR_D_def,dfn'AMOSWAP_W_def,dfn'AMOSWAP_D_def,dfn'SW_def,dfn'SH_def,dfn'SB_def,dfn'SD_def,dfn'SC_W_def,matchLoadReservation_def,ReserveLoad_def,write'ReserveLoad_def,dfn'LW_def,dfn'LWU_def,dfn'LH_def,dfn'LHU_def,dfn'LB_def,dfn'LBU_def,dfn'LD_def,gpr_def,GPR_def,write'gpr_def,write'GPR_def,signalAddressException_def,signalException_def,setTrap_def,write'NextFetch_def,architecture_def,curArch_def,in32BitMode_def,translateAddr_def,vmType_def,privilege_def,MCSR_def,TLBEntry_fn_updates,SV_PTE_fn_updates,translate64_def,curASID_def,ASID_SIZE_def,SCSR_def,TLB_def,write'TLB_def,addToTLB_def,mkTLBEntry_def,lookupTLB_def,FOR_def,walk64_def,rawReadData_def,rawWriteData_def,MEM_def,write'MEM_def,rec'SV_Vaddr_def,rec'SV_PTE_def,reg'SV_PTE_def,checkMemPermission_def,isGlobal_def,LEVEL_BITS_def,PAGESIZE_BITS_def,TLBEntries_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "amoadd_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_w_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_misaligned_4_rd3" ``let c=7w:word8; a=4w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_misaligned_5_rd3" ``let c=7w:word8; a=5w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 5w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_misaligned_6_rd3" ``let c=7w:word8; a=6w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 6w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoadd_d_misaligned_7_rd3" ``let c=7w:word8; a=7w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 7w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOADD_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_w_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_misaligned_4_rd3" ``let c=7w:word8; a=4w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_misaligned_5_rd3" ``let c=7w:word8; a=5w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 5w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_misaligned_6_rd3" ``let c=7w:word8; a=6w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 6w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoxor_d_misaligned_7_rd3" ``let c=7w:word8; a=7w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 7w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOXOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_w_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_misaligned_4_rd3" ``let c=7w:word8; a=4w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_misaligned_5_rd3" ``let c=7w:word8; a=5w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 5w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_misaligned_6_rd3" ``let c=7w:word8; a=6w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 6w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoand_d_misaligned_7_rd3" ``let c=7w:word8; a=7w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 7w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOAND_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_aligned_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_aligned_rd0" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,0w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_aligned_rd2" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,2w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_positive_memory_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(1311768465173141119 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_rs2_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,0w) s in
 (w2n(GPR 0w r),w2n(r.c_gpr c 0w),w2n(r.c_gpr(c+1w) 0w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_address_wrap_rd3" ``let c=7w:word8; a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 18446744073709551615w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_core_wrap_rd3" ``let c=255w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_rv32_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=0w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_rv128_mode_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=3w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_write_walk_returned_state_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3079 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_read_only_page_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(3077 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_invalid_pte_fault_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=9w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(0 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_rs1_zero_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 99w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,0w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_w_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_W (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_overflow_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 18446744073709551615w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18446744073709551615 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_order_0_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_order_1_0_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (1w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_order_1_1_rd3" ``let c=7w:word8; a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 0w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (1w,1w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_misaligned_1_rd3" ``let c=7w:word8; a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 1w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_misaligned_2_rd3" ``let c=7w:word8; a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 2w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_misaligned_3_rd3" ``let c=7w:word8; a=3w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 3w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_misaligned_4_rd3" ``let c=7w:word8; a=4w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 4w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_misaligned_5_rd3" ``let c=7w:word8; a=5w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 5w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_misaligned_6_rd3" ``let c=7w:word8; a=6w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 6w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
val _ = out "amoor_d_misaligned_7_rd3" ``let c=7w:word8; a=7w:word64;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;exception:=NoException;c_NextFetch:=(\id. NONE);c_gpr:=(\id reg. if reg=2w then 7w else if reg=3w then 81985529216486895w else 99w);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with <|mstatus:=((ARB:mstatus) with <|MMPRV:=F;MPRV:=0w;MPRV1:=3w;VM:=0w|>);mcpuid:=((ARB:mcpuid) with ArchBase:=2w)|>);c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if w2n(x-a)<8 then n2w(18364758546640568448 DIV (2 ** (8 * w2n(x-a)))) else 0w)|>); r=dfn'AMOOR_D (0w,0w,3w,2w,3w) s in
 (w2n(GPR 3w r),w2n(r.c_gpr c 3w),w2n(r.c_gpr(c+1w) 3w),
 (case r.c_NextFetch c of SOME (Trap t) => (if t.trap=AMO_Misaligned then 3 else if t.trap=Store_AMO_Fault then 4 else if t.trap=Illegal_Instr then 2 else 5,OPTION_MAP w2n t.badaddr) | _ => (0,NONE)),
 r.exception=NoException,w2n(rawReadData 0w r),w2n(rawReadData 8w r),w2n(rawReadData a r),MAP (\i. w2n(r.MEM8(a+n2w i))) (COUNT_LIST 8),
 OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,e.pte.PTE_D,w2n e.pte.PTE_PPNi,e.pte.PTE_R,w2n e.pte.PTE_SW,w2n e.pte.PTE_T,e.pte.PTE_V,w2n e.pte.sv_pte'rst)) (r.c_tlb c 0w),
 OPTION_MAP (\e. w2n e.pAddr) (r.c_tlb(c+1w) 0w),
 (r with <|c_gpr:=s.c_gpr;MEM8:=s.MEM8;c_tlb:=s.c_tlb;c_NextFetch:=s.c_NextFetch;exception:=s.exception|>)=s,r.totalCore,w2n r.procID)``;
