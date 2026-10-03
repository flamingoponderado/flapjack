val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = (print "updatePC_type="; print_type (type_of ``riscv_step$update_pc``); print "\n");
val _ = print ("updatePC_hypotheses=" ^ Int.toString (length (hyp update_pc_def)) ^ "\n");
fun check label q =
  let val th = prove(q, SIMP_TAC (srw_ss()) [update_pc_def,write'PC_def,combinTheory.UPDATE_def] THEN METIS_TAC [])
  in if null (hyp th) andalso aconv (concl th) q
     then (print(label ^ "="); print_term(concl th); print "\n")
     else raise Fail "update_pc complete equation proof mismatch" end;
val _ = check "updatePC_some_equation" ``!v s. riscv_step$update_pc v s = SOME (riscv$write'PC v s)``;
val _ = print "updatePC_some_proof=T\n";
val _ = check "updatePC_fullRecord_equation" ``!v s. riscv_step$update_pc v s = SOME (s with c_PC := (s.procID =+ v) s.c_PC)``;
val _ = print "updatePC_fullRecord_proof=T\n";
