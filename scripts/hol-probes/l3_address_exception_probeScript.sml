load "riscvTheory"; load "wordsLib";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "address_exception_definition" signalAddressException_def;
val _ = (print "address_exception_type=";print_type(type_of ``riscv$signalAddressException``);print "\n");
val _ = computeLib.add_funs [signalAddressException_def,setTrap_def,write'NextFetch_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "load_zero" ``let s=((ARB:riscv_state) with <|procID:=0w;totalCore:=1;c_NextFetch:=(\id. NONE);exception:=NoException|>); r=signalAddressException (Load_Fault,0w) s in
 ((case r.c_NextFetch 0w of SOME (Trap t) => (t.trap=Load_Fault,OPTION_MAP w2n t.badaddr) | _ => (F,NONE)),r.c_NextFetch (0w+1w)=NONE,r.exception=NoException,r.totalCore,w2n r.procID)``;
val _ = out "store_max" ``let s=((ARB:riscv_state) with <|procID:=255w;totalCore:=1;c_NextFetch:=(\id. NONE);exception:=NoException|>); r=signalAddressException (Store_AMO_Fault,18446744073709551615w) s in
 ((case r.c_NextFetch 255w of SOME (Trap t) => (t.trap=Store_AMO_Fault,OPTION_MAP w2n t.badaddr) | _ => (F,NONE)),r.c_NextFetch (255w+1w)=NONE,r.exception=NoException,r.totalCore,w2n r.procID)``;
val _ = out "misaligned" ``let s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;c_NextFetch:=(\id. NONE);exception:=NoException|>); r=signalAddressException (AMO_Misaligned,3w) s in
 ((case r.c_NextFetch 7w of SOME (Trap t) => (t.trap=AMO_Misaligned,OPTION_MAP w2n t.badaddr) | _ => (F,NONE)),r.c_NextFetch (7w+1w)=NONE,r.exception=NoException,r.totalCore,w2n r.procID)``;
val _ = out "arbitrary_exception" ``let s=((ARB:riscv_state) with <|procID:=7w;totalCore:=1;c_NextFetch:=(\id. NONE);exception:=NoException|>); r=signalAddressException (Illegal_Instr,1234w) s in
 ((case r.c_NextFetch 7w of SOME (Trap t) => (t.trap=Illegal_Instr,OPTION_MAP w2n t.badaddr) | _ => (F,NONE)),r.c_NextFetch (7w+1w)=NONE,r.exception=NoException,r.totalCore,w2n r.procID)``;
OS.Process.exit OS.Process.success;
