loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
            (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;

val _ = Globals.show_types := true;

fun stmt label th =
  (print (label ^ "="); print_term (concl th); print "\n");

fun hyps label th =
  (print (label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));

val _ = hyps "divu_hypotheses" DIVU;
val _ = stmt "divu_statement" DIVU;
val _ = hyps "divu_nop_hypotheses" DIVU_NOP;
val _ = stmt "divu_nop_statement" DIVU_NOP;
val _ = print "source=HOL riscv_stepScript.sml:881 DIVU = arithr [] over dfn'DIVU_def with the rd = 0w companion avoided; per-theorem Thm.hyp captured above; the 64/32-bit widening is unconditional (avoid []), so the sole write hypothesis is rd <> 0w and the DIVU_NOP companion adds rd = 0w\n";
