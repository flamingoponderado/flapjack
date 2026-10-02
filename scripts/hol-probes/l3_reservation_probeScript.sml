load "riscvTheory"; load "wordsLib";
open HolKernel Parse bossLib Tactical Tactic Conv riscvTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "reserve_read_definition" ReserveLoad_def;
val _ = (print "reserve_read_type=";print_type(type_of ``riscv$ReserveLoad``);print "\n");
val _ = definition "reserve_write_definition" write'ReserveLoad_def;
val _ = (print "reserve_write_type=";print_type(type_of ``riscv$write'ReserveLoad``);print "\n");
val _ = definition "reserve_match_definition" matchLoadReservation_def;
val _ = (print "reserve_match_type=";print_type(type_of ``riscv$matchLoadReservation``);print "\n");
val _ = computeLib.add_funs [ReserveLoad_def,write'ReserveLoad_def,matchLoadReservation_def];
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then(print(label^"=");print_term(snd(dest_eq(concl th)));print "\n") else raise Fail "assumptions" end;
val _ = out "none_none" ``let c=7w:word8; v=0w:word64; n=NONE:word64 option;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_ReserveLoad:=(\id. if id=c then NONE else SOME 77w)|>); r=write'ReserveLoad n s in
 (OPTION_MAP w2n(ReserveLoad s),OPTION_MAP w2n(ReserveLoad r),matchLoadReservation v s,matchLoadReservation v r,
 OPTION_MAP w2n(r.c_ReserveLoad(c+1w)),r=(s with c_ReserveLoad:=((c =+ n) s.c_ReserveLoad)),r.totalCore,w2n r.procID)``;
val _ = out "none_zero" ``let c=7w:word8; v=0w:word64; n=SOME 0w:word64 option;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_ReserveLoad:=(\id. if id=c then NONE else SOME 77w)|>); r=write'ReserveLoad n s in
 (OPTION_MAP w2n(ReserveLoad s),OPTION_MAP w2n(ReserveLoad r),matchLoadReservation v s,matchLoadReservation v r,
 OPTION_MAP w2n(r.c_ReserveLoad(c+1w)),r=(s with c_ReserveLoad:=((c =+ n) s.c_ReserveLoad)),r.totalCore,w2n r.procID)``;
val _ = out "clear_zero" ``let c=7w:word8; v=0w:word64; n=NONE:word64 option;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_ReserveLoad:=(\id. if id=c then SOME 0w else SOME 77w)|>); r=write'ReserveLoad n s in
 (OPTION_MAP w2n(ReserveLoad s),OPTION_MAP w2n(ReserveLoad r),matchLoadReservation v s,matchLoadReservation v r,
 OPTION_MAP w2n(r.c_ReserveLoad(c+1w)),r=(s with c_ReserveLoad:=((c =+ n) s.c_ReserveLoad)),r.totalCore,w2n r.procID)``;
val _ = out "replace_match" ``let c=7w:word8; v=123w:word64; n=SOME 123w:word64 option;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_ReserveLoad:=(\id. if id=c then SOME 21w else SOME 77w)|>); r=write'ReserveLoad n s in
 (OPTION_MAP w2n(ReserveLoad s),OPTION_MAP w2n(ReserveLoad r),matchLoadReservation v s,matchLoadReservation v r,
 OPTION_MAP w2n(r.c_ReserveLoad(c+1w)),r=(s with c_ReserveLoad:=((c =+ n) s.c_ReserveLoad)),r.totalCore,w2n r.procID)``;
val _ = out "max_mismatch" ``let c=7w:word8; v=0w:word64; n=SOME 18446744073709551615w:word64 option;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_ReserveLoad:=(\id. if id=c then SOME 18446744073709551615w else SOME 77w)|>); r=write'ReserveLoad n s in
 (OPTION_MAP w2n(ReserveLoad s),OPTION_MAP w2n(ReserveLoad r),matchLoadReservation v s,matchLoadReservation v r,
 OPTION_MAP w2n(r.c_ReserveLoad(c+1w)),r=(s with c_ReserveLoad:=((c =+ n) s.c_ReserveLoad)),r.totalCore,w2n r.procID)``;
val _ = out "present_mismatch" ``let c=7w:word8; v=22w:word64; n=SOME 21w:word64 option;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_ReserveLoad:=(\id. if id=c then SOME 21w else SOME 77w)|>); r=write'ReserveLoad n s in
 (OPTION_MAP w2n(ReserveLoad s),OPTION_MAP w2n(ReserveLoad r),matchLoadReservation v s,matchLoadReservation v r,
 OPTION_MAP w2n(r.c_ReserveLoad(c+1w)),r=(s with c_ReserveLoad:=((c =+ n) s.c_ReserveLoad)),r.totalCore,w2n r.procID)``;
val _ = out "core_zero" ``let c=0w:word8; v=18446744073709551615w:word64; n=SOME 18446744073709551615w:word64 option;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_ReserveLoad:=(\id. if id=c then NONE else SOME 77w)|>); r=write'ReserveLoad n s in
 (OPTION_MAP w2n(ReserveLoad s),OPTION_MAP w2n(ReserveLoad r),matchLoadReservation v s,matchLoadReservation v r,
 OPTION_MAP w2n(r.c_ReserveLoad(c+1w)),r=(s with c_ReserveLoad:=((c =+ n) s.c_ReserveLoad)),r.totalCore,w2n r.procID)``;
val _ = out "core_wrap" ``let c=255w:word8; v=0w:word64; n=SOME 0w:word64 option;
 s=((ARB:riscv_state) with <|procID:=c;totalCore:=1;c_ReserveLoad:=(\id. if id=c then SOME 21w else SOME 77w)|>); r=write'ReserveLoad n s in
 (OPTION_MAP w2n(ReserveLoad s),OPTION_MAP w2n(ReserveLoad r),matchLoadReservation v s,matchLoadReservation v r,
 OPTION_MAP w2n(r.c_ReserveLoad(c+1w)),r=(s with c_ReserveLoad:=((c =+ n) s.c_ReserveLoad)),r.totalCore,w2n r.procID)``;
OS.Process.exit OS.Process.success;
