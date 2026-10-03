load "riscvTheory"; load "wordsLib"; load "state_transformerTheory";
open HolKernel Parse bossLib Tactical Tactic boolSyntax Conv riscvTheory state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "model_fetch_full_definition" Fetch_def;
val _ = (print "model_fetch_full_type=";print_type(type_of ``riscv$Fetch``);print "\n");
val _ = definition "model_fetch_odd_generic_equation" (prove(``word_bit 0 (PC s) ==> Fetch () s = (F_Error (Internal (FETCH_MISALIGNED (PC s))),s)``,STRIP_TAC THEN ASM_SIMP_TAC(srw_ss())[Fetch_def,boolTheory.LET_DEF]));
val _ = computeLib.add_funs [Fetch_def,PC_def,Delta_def,write'Delta_def,rawReadInst_def,write'Skip_def,boolify8_def,translateAddr_def,vmType_def,privilege_def,MCSR_def,TLBEntry_fn_updates,SV_PTE_fn_updates,translate64_def,curASID_def,ASID_SIZE_def,SCSR_def,TLB_def,write'TLB_def,addToTLB_def,mkTLBEntry_def,lookupTLB_def,FOR_def,walk64_def,rawReadData_def,rawWriteData_def,MEM_def,write'MEM_def,rec'SV_Vaddr_def,rec'SV_PTE_def,reg'SV_PTE_def,checkMemPermission_def,isGlobal_def,LEVEL_BITS_def,PAGESIZE_BITS_def,TLBEntries_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "odd_unknown_vm" ``let a=1w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 1w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=31w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "odd_wrap" ``let a=18446744073709551615w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 18446744073709551615w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=9w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "none_vm_1" ``let a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 2w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=1w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "none_vm_2" ``let a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 2w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=2w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "none_vm_8" ``let a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 2w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=8w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "none_vm_11" ``let a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 2w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=11w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "none_vm_12" ``let a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 2w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=12w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "bare_0_0" ``let a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 0w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=0w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 0w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "bare_0_3" ``let a=0w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 0w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=0w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "bare_2_3" ``let a=2w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 2w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=0w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "bare_18446744073709551614_0" ``let a=18446744073709551614w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 18446744073709551614w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=0w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 0w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "bare_18446744073709551614_3" ``let a=18446744073709551614w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 18446744073709551614w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=0w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "hit_sv39" ``let a=9848w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 1656w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=9w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. if j=4w then SOME (<|age:=88w;asid:=63w;global:=F;pAddr:=8192w;pte:=(rec'SV_PTE 3079w);pteAddr:=0w;vAddr:=0w;vAddrMask:=4095w;vMatchMask:=18446744073709547520w|>) else NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "hit_sv48_half" ``let a=9848w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 1656w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=10w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. if j=4w then SOME (<|age:=88w;asid:=63w;global:=F;pAddr:=8192w;pte:=(rec'SV_PTE 3079w);pteAddr:=0w;vAddr:=0w;vAddrMask:=4095w;vMatchMask:=18446744073709547520w|>) else NONE);
 MEM8:=(\x. if x=a then 0w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "hit_denied" ``let a=9848w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 1656w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=1w;MPRV1:=3w;VM:=9w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. if j=4w then SOME (<|age:=88w;asid:=63w;global:=F;pAddr:=8192w;pte:=(rec'SV_PTE 3079w);pteAddr:=0w;vAddr:=0w;vAddrMask:=4095w;vMatchMask:=18446744073709547520w|>) else NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "walk_sv39" ``let a=13944w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 1656w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=9w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(3079 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "walk_sv48" ``let a=13944w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 1656w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=10w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 0w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(3079 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
val _ = out "walk_invalid" ``let a=13944w:word64;
 s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;exception:=NoException;c_PC:=(\id. 1656w);c_Skip:=(\id. 99w);c_update:=(\id. <|addr:=SOME 21w;data1:=SOME 22w;data2:=SOME 23w;exc_taken:=T;fetch_exc:=T;fp_data:=SOME 24w;pc:=11w;rinstr:=Half 48879w;st_width:=SOME 8w|>);c_cycles:=(\id. 77w);
 c_MCSR:=(\id. (ARB:MachineCSR) with mstatus:=((ARB:mstatus) with <|MMPRV:=T;MPRV:=0w;MPRV1:=3w;VM:=9w|>));c_SCSR:=(\id. (ARB:SupervisorCSR) with <|sasid:=63w;sptbr:=0w|>);c_tlb:=(\id j. NONE);
 MEM8:=(\x. if x=a then 3w else if x=a+1w then 18w else if x=a+2w then 52w else if x=a+3w then 86w else if w2n x < 8 then n2w(0 DIV (2 ** (8 * w2n x))) else 0w)|>);
 r=riscv$Fetch () s in ((case FST r of F_Result (Half w) => (0,16,w2n w) | F_Result (Word w) => (0,32,w2n w) | F_Error (Internal (FETCH_MISALIGNED v)) => (1,0,w2n v) | F_Error (Internal (FETCH_FAULT v)) => (2,0,w2n v) | _ => (3,0,0)),
 w2n ((SND r).c_Skip 7w),w2n ((SND r).c_Skip 8w),
 MAP (\id. let d=(SND r).c_update id in (d.exc_taken,d.fetch_exc,w2n d.pc,(case d.rinstr of Half w => (16,w2n w) | Word w => (32,w2n w)),OPTION_MAP w2n d.addr,OPTION_MAP w2n d.data1,OPTION_MAP w2n d.data2,OPTION_MAP w2n d.fp_data,OPTION_MAP w2n d.st_width)) [7w;8w],
 w2n(rawReadData 0w (SND r)),
 MAP (\j. OPTION_MAP (\e. (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))) ((SND r).c_tlb 7w (n2w j))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15],
 (SND r).exception=NoException,w2n((SND r).MEM8 a),(SND r).totalCore,w2n((SND r).procID))``;
