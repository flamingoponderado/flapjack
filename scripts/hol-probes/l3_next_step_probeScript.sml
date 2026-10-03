val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = (print "NextRISCV_type="; print_type (type_of ``riscv_step$NextRISCV``); print "\n");
val _ = print ("NextRISCV_hypotheses=" ^ Int.toString (length (hyp NextRISCV_def)) ^ "\n");
val equation = ``!s. riscv_step$NextRISCV s =
  let (f,s) = riscv_step$Fetch s in
  let s = riscv$Run (riscv_step$DecodeAny f) s in
  if s.exception <> riscv$NoException then NONE else
    let pc = riscv$PC s in
    case riscv$NextFetch s of
      NONE => riscv_step$update_pc (pc + riscv$Skip s) s
    | SOME (riscv$BranchTo a) => riscv_step$update_pc a (riscv$write'NextFetch NONE s)
    | _ => NONE``;
val th = prove(equation, SIMP_TAC (srw_ss()) [NextRISCV_def]);
val _ = if null(hyp th) andalso aconv (concl th) equation then ()
  else raise Fail "full NextRISCV equation proof mismatch";
val _ = (print "NextRISCV_equation="; print_term(concl th); print "\n");
val _ = print "NextRISCV_proof=T\n";
