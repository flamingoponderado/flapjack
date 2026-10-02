load "riscvTheory"; load "wordsLib";
open HolKernel Parse bossLib Tactical boolSyntax Conv riscvTheory;
val _=Globals.linewidth:=100000;
val _=computeLib.add_funs [mkTLBEntry_def,LEVEL_BITS_def,PAGESIZE_BITS_def,rec'SV_PTE_def,reg'SV_PTE_def];
fun out label q=let val th=(EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL)q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _=out "entry_0" ``let e=mkTLBEntry(63w,T,0x123456789ABCDEF0w,0xFEDCBA9876543210w,rec'SV_PTE 0x123456789ABCDEF0w,0,0x12345678w)((ARB:riscv_state) with <|procID:=7w;totalCore:=1;c_cycles:=(\id.77w)|>) in (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))``;
val _=out "entry_1" ``let e=mkTLBEntry(63w,T,0x123456789ABCDEF0w,0xFEDCBA9876543210w,rec'SV_PTE 0x123456789ABCDEF0w,1,0x12345678w)((ARB:riscv_state) with <|procID:=7w;totalCore:=1;c_cycles:=(\id.77w)|>) in (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))``;
val _=out "entry_5" ``let e=mkTLBEntry(63w,T,0x123456789ABCDEF0w,0xFEDCBA9876543210w,rec'SV_PTE 0x123456789ABCDEF0w,5,0x12345678w)((ARB:riscv_state) with <|procID:=7w;totalCore:=1;c_cycles:=(\id.77w)|>) in (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))``;
val _=out "entry_6" ``let e=mkTLBEntry(63w,T,0x123456789ABCDEF0w,0xFEDCBA9876543210w,rec'SV_PTE 0x123456789ABCDEF0w,6,0x12345678w)((ARB:riscv_state) with <|procID:=7w;totalCore:=1;c_cycles:=(\id.77w)|>) in (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))``;
val _=out "entry_7" ``let e=mkTLBEntry(63w,T,0x123456789ABCDEF0w,0xFEDCBA9876543210w,rec'SV_PTE 0x123456789ABCDEF0w,7,0x12345678w)((ARB:riscv_state) with <|procID:=7w;totalCore:=1;c_cycles:=(\id.77w)|>) in (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))``;
val _=out "entry_1000" ``let e=mkTLBEntry(63w,T,0x123456789ABCDEF0w,0xFEDCBA9876543210w,rec'SV_PTE 0x123456789ABCDEF0w,1000,0x12345678w)((ARB:riscv_state) with <|procID:=7w;totalCore:=1;c_cycles:=(\id.77w)|>) in (w2n e.asid,e.global,w2n e.vAddrMask,w2n e.vMatchMask,w2n e.vAddr,w2n e.pAddr,w2n e.age,w2n e.pteAddr,w2n(reg'SV_PTE e.pte))``;

val _=computeLib.add_funs [lookupTLB_def,TLBEntries_def,state_transformerTheory.FOR_def];
val _=out "lookup_empty" ``let e=(ARB:TLBEntry) with <|asid:=5w;global:=F;vAddr:=305418240w;vMatchMask:=18446744073709547520w|> in OPTION_MAP (\(e,i).w2n i) (lookupTLB(5w,0x12345678w,\i.if F then SOME e else NONE))``;
val _=out "lookup_first" ``let e=(ARB:TLBEntry) with <|asid:=5w;global:=F;vAddr:=305418240w;vMatchMask:=18446744073709547520w|> in OPTION_MAP (\(e,i).w2n i) (lookupTLB(5w,0x12345678w,\i.if i=0w then SOME e else NONE))``;
val _=out "lookup_last" ``let e=(ARB:TLBEntry) with <|asid:=5w;global:=F;vAddr:=305418240w;vMatchMask:=18446744073709547520w|> in OPTION_MAP (\(e,i).w2n i) (lookupTLB(5w,0x12345678w,\i.if i=15w then SOME e else NONE))``;
val _=out "lookup_two" ``let e=(ARB:TLBEntry) with <|asid:=5w;global:=F;vAddr:=305418240w;vMatchMask:=18446744073709547520w|> in OPTION_MAP (\(e,i).w2n i) (lookupTLB(5w,0x12345678w,\i.if i=2w \/ i=6w then SOME e else NONE))``;
val _=out "lookup_wrong_asid" ``let e=(ARB:TLBEntry) with <|asid:=6w;global:=F;vAddr:=305418240w;vMatchMask:=18446744073709547520w|> in OPTION_MAP (\(e,i).w2n i) (lookupTLB(5w,0x12345678w,\i.if i=2w then SOME e else NONE))``;
val _=out "lookup_global" ``let e=(ARB:TLBEntry) with <|asid:=6w;global:=T;vAddr:=305418240w;vMatchMask:=18446744073709547520w|> in OPTION_MAP (\(e,i).w2n i) (lookupTLB(5w,0x12345678w,\i.if i=2w then SOME e else NONE))``;
val _=out "lookup_wrong_address" ``let e=(ARB:TLBEntry) with <|asid:=5w;global:=F;vAddr:=305422336w;vMatchMask:=18446744073709547520w|> in OPTION_MAP (\(e,i).w2n i) (lookupTLB(5w,0x12345678w,\i.if i=2w then SOME e else NONE))``;
val _=out "lookup_zero_mask" ``let e=(ARB:TLBEntry) with <|asid:=6w;global:=T;vAddr:=0w;vMatchMask:=0w|> in OPTION_MAP (\(e,i).w2n i) (lookupTLB(5w,0x12345678w,\i.if i=3w then SOME e else NONE))``;
