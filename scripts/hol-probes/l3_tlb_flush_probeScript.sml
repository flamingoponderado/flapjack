load "riscvTheory"; load "wordsLib"; load "state_transformerTheory";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "flush_definition" flushTLB_def;
val _ = definition "sfence_definition" dfn'SFENCE_VM_def;
val _ = (print "flush_type=";print_type(type_of ``riscv$flushTLB``);print "\n");
val _ = (print "sfence_type=";print_type(type_of ``riscv$dfn'SFENCE_VM``);print "\n");
val _ = computeLib.add_funs [flushTLB_def,dfn'SFENCE_VM_def,FOR_def,TLBEntries_def,curASID_def,ASID_SIZE_def,SCSR_def,TLB_def,write'TLB_def,GPR_def,gpr_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "flush_asid0_addrnone" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (0w,NONE,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid0_addr0" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (0w,SOME 0w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid0_addr1" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (0w,SOME 1w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid0_addr4096" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (0w,SOME 4096w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid3_addrnone" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (3w,NONE,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid3_addr0" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (3w,SOME 0w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid3_addr1" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (3w,SOME 1w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid3_addr4096" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (3w,SOME 4096w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid4_addrnone" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (4w,NONE,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid4_addr0" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (4w,SOME 0w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid4_addr1" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (4w,SOME 1w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid4_addr4096" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (4w,SOME 4096w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid63_addrnone" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (63w,NONE,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid63_addr0" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (63w,SOME 0w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid63_addr1" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (63w,SOME 1w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "flush_asid63_addr4096" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let r=flushTLB (63w,SOME 4096w,tab) in (MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16))``;
val _ = out "sfence_asid0_rs0_addr0_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs0_addr0_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs0_addr1_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs0_addr1_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs0_addr4096_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs0_addr4096_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs2_addr0_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs2_addr0_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs2_addr1_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs2_addr1_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs2_addr4096_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid0_rs2_addr4096_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=0w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs0_addr0_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs0_addr0_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs0_addr1_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs0_addr1_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs0_addr4096_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs0_addr4096_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs2_addr0_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs2_addr0_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs2_addr1_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs2_addr1_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs2_addr4096_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid3_rs2_addr4096_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=3w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs0_addr0_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs0_addr0_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs0_addr1_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs0_addr1_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs0_addr4096_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs0_addr4096_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs2_addr0_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs2_addr0_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs2_addr1_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs2_addr1_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs2_addr4096_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid4_rs2_addr4096_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=4w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs0_addr0_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs0_addr0_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs0_addr1_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs0_addr1_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs0_addr4096_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs0_addr4096_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 0w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs2_addr0_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs2_addr0_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 0w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs2_addr1_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs2_addr1_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 1w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs2_addr4096_core7" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=7w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
val _ = out "sfence_asid63_rs2_addr4096_core255" ``let e=((ARB:TLBEntry) with <|asid:=3w;global:=F;vAddr:=0w;vMatchMask:=4095w|>);
 tab=(\j:word4. if j=3w then NONE else if j=1w then SOME(e with global:=T) else if j=2w then SOME(e with asid:=4w) else if j=4w then SOME(e with vAddr:=4096w) else if j=0w \/ j=14w \/ j=15w then SOME e else NONE) in let c=255w:word8;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_tlb:=(\id. tab);c_gpr:=(\id reg. if reg=2w then 4096w else 99w);c_SCSR:=(\id. (ARB:SupervisorCSR) with sasid:=63w)|>);
 t=dfn'SFENCE_VM 2w s; r=t.c_tlb c in ((MAP (\i. IS_SOME(r(n2w i))) (COUNT_LIST 16),
 MAP (\i. if IS_SOME(r(n2w i)) then r(n2w i)=tab(n2w i) else T) (COUNT_LIST 16)),t.c_tlb(c+1w)=tab,(t with c_tlb:=s.c_tlb)=s,t.totalCore,w2n t.procID)``;
