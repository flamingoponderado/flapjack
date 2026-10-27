load "export_riscvTheory"; load "mlstringSyntax"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val result = EVAL ``mlstring$concat (misc$append
 (export_riscv$riscv_export [«put»;«get»] [0w;171w;255w] [4w;17w]
  [(«a+»,2,4);(«F»,6,3)] [] F F))``;
val bytes = mlstringSyntax.dest_mlstring (rhs (concl result)) |> String.explode |> map (Int.toString o Char.ord);
val _ = (print "assembly="; print (String.concatWith "," bytes); print "\nend=ok\n");
