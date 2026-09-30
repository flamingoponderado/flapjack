load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "load16"
  ``apply_colour_inst (\n. n + 10) (Mem Load16 3 (Addr 5 7w) : 8 asm$inst)``;
val _ = observe "store16"
  ``apply_colour_inst (\n. n + 10) (Mem Store16 3 (Addr 5 7w) : 8 asm$inst)``;
val _ = observe "load8"
  ``apply_colour_inst (\n. n + 10) (Mem Load8 3 (Addr 5 7w) : 8 asm$inst)``;
val _ = observe "store32"
  ``apply_colour_inst (\n. n + 10) (Mem Store32 3 (Addr 5 7w) : 8 asm$inst)``;
val _ = observe "carry"
  ``apply_colour_inst (\n. n + 10) (Arith (AddCarry 1 2 3 4) : 8 asm$inst)``;
val _ = observe "fp_move"
  ``apply_colour_inst (\n. n + 10) (FP (FPMovFromReg 1 2 3) : 8 asm$inst)``;
