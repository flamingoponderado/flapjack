load "preamble";
load "asmPropsTheory";
open preamble HolKernel Parse boolLib bossLib asmPropsTheory;
fun ty label tm = print(label ^ "=" ^ type_to_string(type_of tm) ^ "\n");
fun eqn label tm defs = let val th = prove(tm, SIMP_TAC (srw_ss()) defs) in
 if aconv(concl th) tm andalso null(hyp th) then print(label ^ "=T\n")
 else raise Fail label end;
val _ = ty "offset_monotonic_type" ``offset_monotonic``;
val _ = ty "enc_ok_type" ``enc_ok``;
val _ = ty "target_ok_type" ``target_ok``;
val _ = eqn "offset_monotonic_full" ``!enc c a1 a2 i1 i2.
 offset_monotonic enc c a1 a2 i1 i2 <=>
 (asm_ok i1 c /\ asm_ok i2 c ==>
 (0w <= a1 /\ 0w <= a2 /\ a1 <= a2 ==> LENGTH(enc i1) <= LENGTH(enc i2)) /\
 (a1 < 0w /\ a2 < 0w /\ a2 <= a1 ==> LENGTH(enc i1) <= LENGTH(enc i2)))`` [offset_monotonic_def];
val _ = eqn "enc_ok_full" ``!c. enc_ok c <=>
 (2 EXP c.code_alignment = LENGTH(c.encode (Inst Skip))) /\
 (!w. LENGTH(c.encode w) MOD 2 EXP c.code_alignment = 0 /\ LENGTH(c.encode w) <> 0) /\
 (!w1 w2. offset_monotonic c.encode c w1 w2 (Jump w1) (Jump w2)) /\
 (!cmp r ri w1 w2. offset_monotonic c.encode c w1 w2 (JumpCmp cmp r ri w1) (JumpCmp cmp r ri w2)) /\
 (!w1 w2. offset_monotonic c.encode c w1 w2 (Call w1) (Call w2)) /\
 (!w1 w2 r. offset_monotonic c.encode c w1 w2 (Loc r w1) (Loc r w2))`` [enc_ok_def];
val _ = eqn "target_ok_full" ``!t. target_ok t <=> enc_ok t.config /\
 !ms1 ms2 s. t.proj s.mem_domain ms1 = t.proj s.mem_domain ms2 ==>
 (target_state_rel t s ms1 = target_state_rel t s ms2) /\
 (t.state_ok ms1 = t.state_ok ms2) /\ (t.get_pc ms1 = t.get_pc ms2) /\
 (!a. a IN s.mem_domain ==> t.get_byte ms1 a = t.get_byte ms2 a)`` [target_ok_def];
val _ = let val th = EVAL ``((0w:1 word) <= 0w) /\ ~((0w:1 word) <= 1w) /\ ((1w:1 word) < 0w) /\ ((1w:1 word) <= 1w)`` in
 if aconv(rhs(concl th)) ``T`` andalso null(hyp th) then print "signed_offsets_1=T\n"
 else raise Fail "signed_offsets_1" end;
val _ = let val th = EVAL ``((0w:2 word) <= 1w) /\ ~((0w:2 word) <= 2w) /\ ((2w:2 word) < 0w) /\ ((2w:2 word) <= 3w)`` in
 if aconv(rhs(concl th)) ``T`` andalso null(hyp th) then print "signed_offsets_2=T\n"
 else raise Fail "signed_offsets_2" end;
val _ = let val th = EVAL ``((0w:8 word) <= 127w) /\ ~((0w:8 word) <= 128w) /\ ((128w:8 word) < 0w) /\ ((128w:8 word) <= 255w)`` in
 if aconv(rhs(concl th)) ``T`` andalso null(hyp th) then print "signed_offsets_8=T\n"
 else raise Fail "signed_offsets_8" end;
val _ = let val th = EVAL ``((0w:32 word) <= 2147483647w) /\ ~((0w:32 word) <= 2147483648w) /\ ((2147483648w:32 word) < 0w) /\ ((2147483648w:32 word) <= 4294967295w)`` in
 if aconv(rhs(concl th)) ``T`` andalso null(hyp th) then print "signed_offsets_32=T\n"
 else raise Fail "signed_offsets_32" end;
val _ = let val th = EVAL ``((0w:64 word) <= 9223372036854775807w) /\ ~((0w:64 word) <= 9223372036854775808w) /\ ((9223372036854775808w:64 word) < 0w) /\ ((9223372036854775808w:64 word) <= 18446744073709551615w)`` in
 if aconv(rhs(concl th)) ``T`` andalso null(hyp th) then print "signed_offsets_64=T\n"
 else raise Fail "signed_offsets_64" end;
val _ = let val th = EVAL ``((0w:80 word) <= 604462909807314587353087w) /\ ~((0w:80 word) <= 604462909807314587353088w) /\ ((604462909807314587353088w:80 word) < 0w) /\ ((604462909807314587353088w:80 word) <= 1208925819614629174706175w)`` in
 if aconv(rhs(concl th)) ``T`` andalso null(hyp th) then print "signed_offsets_80=T\n"
 else raise Fail "signed_offsets_80" end;
val _ = eqn "offset_constant_payload" ``!c a1 a2 i1 i2. offset_monotonic (\i. [T;F]) c a1 a2 i1 i2`` [offset_monotonic_def];
val _ = eqn "enc_constant_valid" ``!c. enc_ok (c with <|encode := (\i. [0w]); code_alignment := 0|>)`` [enc_ok_def,offset_monotonic_def];
val _ = eqn "enc_empty_invalid" ``!c. ~enc_ok (c with encode := (\i. []))`` [enc_ok_def];
val _ = eqn "enc_alignment_invalid" ``!c. ~enc_ok (c with <|encode := (\i. [0w]); code_alignment := 1|>)`` [enc_ok_def];
val _ = OS.Process.exit OS.Process.success;
