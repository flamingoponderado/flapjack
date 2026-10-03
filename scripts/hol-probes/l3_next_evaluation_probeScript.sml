val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
fun check source q =
  let val th = prove(q, METIS_TAC [source])
  in if null(hyp source) andalso null(hyp th) andalso aconv (concl th) q then th
     else raise Fail "original Next evaluation theorem shape or hypotheses changed"
  end;
fun binders label th =
  let val (vars,_) = strip_forall (concl th)
  in print(label ^ "=");
     List.app (fn v => (print(fst(dest_var v) ^ ":"); print_type(type_of v); print ";")) vars;
     print "\n"
  end;
fun statement label th = (print(label ^ "="); print_term(concl th); print "\n");
val nextEval = check riscv_stepTheory.NextRISCV
  ``!s w fetched i nxt.
    (riscv_step$Fetch s = (w,fetched)) /\
    (riscv_step$DecodeAny w = i) /\
    (riscv$Run i fetched = nxt) /\
    (nxt.exception = riscv$NoException) /\
    (nxt.c_NextFetch nxt.procID = NONE) ==>
    (riscv_step$NextRISCV s = riscv_step$update_pc (nxt.c_PC nxt.procID + riscv$Skip nxt) nxt)``;
val _ = binders "nextEval_binders" nextEval;
val _ = statement "nextEval_statement" nextEval;
val _ = print "nextEval_hypotheses=0\n";
val _ = print "nextEval_proof=T\n";
val nextBranch = check riscv_stepTheory.NextRISCV_branch
  ``!s w fetched i nxt a.
    (riscv_step$Fetch s = (w,fetched)) /\
    (riscv_step$DecodeAny w = i) /\
    (riscv$Run i fetched = nxt) /\
    (nxt.exception = riscv$NoException) /\
    (nxt.c_NextFetch nxt.procID = SOME (riscv$BranchTo a)) ==>
    (riscv_step$NextRISCV s = riscv_step$update_pc a
      (nxt with c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch))``;
val _ = binders "nextBranch_binders" nextBranch;
val _ = statement "nextBranch_statement" nextBranch;
val _ = print "nextBranch_hypotheses=0\n";
val _ = print "nextBranch_proof=T\n";
val nextCond = check riscv_stepTheory.NextRISCV_cond_branch
  ``!s w fetched i nxt a b.
    (riscv_step$Fetch s = (w,fetched)) /\
    (riscv_step$DecodeAny w = i) /\
    (riscv$Run i fetched = nxt) /\
    (nxt.exception = riscv$NoException) /\
    (nxt.c_NextFetch nxt.procID = if b then SOME (riscv$BranchTo a) else NONE) ==>
    (riscv_step$NextRISCV s = riscv_step$update_pc
      (if b then a else nxt.c_PC nxt.procID + riscv$Skip nxt)
      (nxt with c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch))``;
val _ = binders "nextCond_binders" nextCond;
val _ = statement "nextCond_statement" nextCond;
val _ = print "nextCond_hypotheses=0\n";
val _ = print "nextCond_proof=T\n";
