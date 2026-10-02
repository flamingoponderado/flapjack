load "preamble";
load "targetPropsTheory";
open preamble HolKernel Parse boolLib bossLib targetPropsTheory targetSemTheory;
val statement = ``evaluate mc ffi k ms = (r1,ms1,st1) /\ r1 <> TimeOut /\
 evaluate mc ffi k' ms = (r2,ms2,st2) /\ r2 <> TimeOut ==>
 (r1,ms1,st1) = (r2,ms2,st2)``;
val th = prove(statement,
 srw_tac[][] \\ imp_res_tac evaluate_add_clock \\ full_simp_tac(srw_ss())[]
 \\ pop_assum (qspec_then `k'` mp_tac)
 \\ pop_assum (qspec_then `k` mp_tac)
 \\ full_simp_tac(srw_ss())[AC ADD_ASSOC ADD_COMM]);
val _ = if aconv (concl th) statement andalso null(hyp th)
 then print "lt_ignore_full_statement=T\n" else raise Fail "local clock proof mismatch";
val _ = print ("lt_ignore_type=" ^ type_to_string(type_of(concl th)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
