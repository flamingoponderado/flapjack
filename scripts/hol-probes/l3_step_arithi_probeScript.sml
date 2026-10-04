val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
fun typ label q = (print(label ^ "="); print_type(type_of q); print "\n");

val _ = hyps "addi_hypotheses" ADDI;
val _ = stmt "addi_statement" ADDI;
val _ = stmt "slti_statement" SLTI;
val _ = stmt "sltiu_statement" SLTIU;
val _ = stmt "andi_statement" ANDI;
val _ = stmt "ori_statement" ORI;
val _ = stmt "xori_statement" XORI;
val _ = typ "imm12_type" ``(0w : word12)``;
val _ = print "source=HOL riscv_stepScript.sml:837-843 class evaluator over dfn'ADDI/SLTI/SLTIU/ANDI/ORI/XORI_def; sole hypothesis rd <> 0w\n";
