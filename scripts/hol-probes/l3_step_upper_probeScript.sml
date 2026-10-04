val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
fun typ label q = (print(label ^ "="); print_type(type_of q); print "\n");

val _ = hyps "lui_hypotheses" LUI;
val _ = stmt "lui_statement" LUI;
val _ = stmt "auipc_statement" AUIPC;
val _ = typ "imm20_type" ``(0w : word20)``;
val _ = print "source=HOL riscv_stepScript.sml:853-854 class_rd0 evaluator over dfn'LUI/AUIPC_def; sole hypothesis rd <> 0w\n";
