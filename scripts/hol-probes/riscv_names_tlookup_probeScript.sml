load "preamble"; load "riscv_configTheory";
open bossLib HolKernel Parse preamble riscv_configTheory;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "names" ``MAP (tlookup riscv_names) [0;1;2;3;4;10;11;12;13;27;28;29;30;5;31;32;1000]``;
