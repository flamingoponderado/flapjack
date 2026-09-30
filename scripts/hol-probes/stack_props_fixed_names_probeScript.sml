load "bossLib"; load "preamble"; load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val c = ``c:8 asm$asm_config``;
val good = ``sptree$insert 3 2 (sptree$insert 4 1 sptree$LN):num num_map``;
val _ = out "x86_good" ``fixed_names ^good (^c with ISA := asm$x86_64)``;
val _ = out "x86_empty" ``fixed_names sptree$LN (^c with ISA := asm$x86_64)``;
val _ = out "x86_bad_zero" ``fixed_names (sptree$insert 0 9 ^good) (^c with ISA := asm$x86_64)``;
val _ = out "riscv_empty" ``fixed_names sptree$LN (^c with ISA := asm$RISC_V)``;
