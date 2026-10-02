load "preamble";
load "targetSemTheory";
open HolKernel Parse boolLib bossLib targetSemTheory;
fun clause label q =
  let val th = prove(q, REWRITE_TAC [machine_sem_def])
  in if aconv (concl th) q andalso null (hyp th)
     then print(label ^ "=T\n") else raise Fail "clause conclusion/hypothesis mismatch" end;
val _ = clause "ts_terminate_clause" ``machine_sem (mc:('a,'b,'c)machine_config) (ffi:'ffi ffi_state) ms (Terminate outcome events) <=>
  ?k ms' ffi'. evaluate mc ffi k ms = (Halt outcome,ms',ffi') /\ ffi'.io_events = events``;
val _ = clause "ts_diverge_clause" ``machine_sem (mc:('a,'b,'c)machine_config) (ffi:'ffi ffi_state) ms (Diverge trace) <=>
  (!k. ?ms' ffi'. evaluate mc ffi k ms = (TimeOut,ms',ffi')) /\
  lprefix_lub (IMAGE (\k. fromList (SND (SND (evaluate mc ffi k ms))).io_events) UNIV) trace``;
val _ = clause "ts_fail_clause" ``machine_sem (mc:('a,'b,'c)machine_config) (ffi:'ffi ffi_state) ms Fail <=>
  ?k. FST (evaluate mc ffi k ms) = Error``;
val _ = OS.Process.exit OS.Process.success;
