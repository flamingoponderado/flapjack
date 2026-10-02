load "riscv_stepTheory";
open HolKernel Parse bossLib Tactical boolSyntax Conv riscv_stepTheory;
val _ = Globals.linewidth := 100000;
fun definition label th = if null(hyp th) then (print(label^"=");print_term(concl th);print "\n") else raise Fail "hypotheses";
val _ = definition "step_fetch_full_definition" Fetch_def;
val _ = (print "step_fetch_full_type=";print_type(type_of ``riscv_step$Fetch``);print "\n");
val _ = definition "step_fetch_generic_equation" (prove(``riscv_step$Fetch s = let (w,s1) = riscv$translateAddr (riscv$PC s,riscv$Instruction,riscv$Read) s in riscv$rawReadInst (THE w) s1``,SIMP_TAC(srw_ss())[Fetch_def]));
