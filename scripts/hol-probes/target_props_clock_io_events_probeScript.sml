load "preamble";
load "targetPropsTheory";
open preamble HolKernel Parse boolLib bossLib targetPropsTheory targetSemTheory;
val statement = ``!mc ffi k ms k'. k <= k' ==>
 (SND(SND(evaluate mc ffi k ms))).io_events ≼
 (SND(SND(evaluate mc ffi k' ms))).io_events``;
val th = prove(statement, MATCH_ACCEPT_TAC evaluate_add_clock_io_events_mono);
val _ = if aconv (concl th) statement andalso null(hyp th)
 then print "tp_clock_io_full_statement=T\n" else raise Fail "clock IO theorem mismatch";
val _ = print ("tp_clock_io_type=" ^ type_to_string(type_of(concl th)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
