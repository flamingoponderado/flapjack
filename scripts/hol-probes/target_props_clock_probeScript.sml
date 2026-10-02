load "preamble";
load "targetPropsTheory";
open preamble HolKernel Parse boolLib bossLib targetPropsTheory targetSemTheory;
val _ = if null (hyp evaluate_add_clock) then print "tp_clock_theorem_closed=T\n"
  else raise Fail "evaluate_add_clock theorem has hypotheses";
val _ = print ("tp_clock_type=" ^ type_to_string (type_of (concl evaluate_add_clock)) ^ "\n");
val clock_statement = ``!mc ffi k ms extra r ms1 ffi1.
 evaluate mc ffi k ms = (r,ms1,ffi1) /\ r <> TimeOut ==>
 evaluate mc ffi (k+extra) ms = (r,ms1,ffi1)``;
val clock_statement_th = prove(clock_statement, MATCH_ACCEPT_TAC evaluate_add_clock);
val _ = if aconv (concl clock_statement_th) clock_statement andalso null(hyp clock_statement_th)
 then print "tp_clock_statement=T\n" else raise Fail "clock theorem statement mismatch";
fun out label q = (print(label ^ "="); print_term(rconc(CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pred_setTheory.IN_APP])) (EVAL q))); print "\n");
val _ = out "tp_halt_stable" ``let c = (mc:(8,num,num)machine_config) with
 <|prog_addresses:=EMPTY;ffi_entry_pcs:=[];halt_pc:=0w;target:=(mc.target with <|get_pc:=(\ms. 0w);get_reg:=(\ms r. 0w)|>)|>
 in evaluate c (ffi:num ffi_state) 1 7 = evaluate c ffi 5 7``;
val _ = out "tp_error_stable" ``let c = (mc:(8,num,num)machine_config) with
 <|prog_addresses:=EMPTY;ffi_entry_pcs:=[];halt_pc:=1w;ccache_pc:=2w;target:=(mc.target with get_pc:=(\ms. 0w))|>
 in evaluate c (ffi:num ffi_state) 1 7 = evaluate c ffi 5 7``;
val _ = OS.Process.exit OS.Process.success;
