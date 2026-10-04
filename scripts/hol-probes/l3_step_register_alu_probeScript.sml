val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
fun typ label q = (print(label ^ "="); print_type(type_of q); print "\n");

val _ = hyps "add_hypotheses" ADD;
val _ = stmt "add_statement" ADD;
val _ = stmt "sub_statement" SUB;
val _ = stmt "and_statement" AND;
val _ = stmt "or_statement" OR;
val _ = stmt "xor_statement" XOR;
val _ = typ "gpr_op_type" ``(op : word64 -> word64 -> word64)``;
val _ = print "source=HOL riscv_stepScript.sml:858-866 class evaluator over dfn'ADD/SUB/AND/OR/XOR_def; sole hypothesis rd <> 0w\n";
