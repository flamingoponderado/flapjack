load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "skip"
  ``remove_dead_inst (Skip : 8 asm$inst) (LN)``;
val _ = observe "const_dead"
  ``remove_dead_inst (Const 1 7w : 8 asm$inst) (LN)``;
val _ = observe "const_live"
  ``remove_dead_inst (Const 1 7w : 8 asm$inst) (fromAList [(1,())])``;
val _ = observe "load16"
  ``remove_dead_inst (Mem Load16 1 (Addr 2 7w) : 8 asm$inst) (LN)``;
val _ = observe "store16"
  ``remove_dead_inst (Mem Store16 1 (Addr 2 7w) : 8 asm$inst) (LN)``;
val _ = observe "store32"
  ``remove_dead_inst (Mem Store32 1 (Addr 2 7w) : 8 asm$inst) (LN)``;
val _ = observe "load8"
  ``remove_dead_inst (Mem Load8 1 (Addr 2 7w) : 8 asm$inst) (LN)``;
val _ = observe "carry_live"
  ``remove_dead_inst (Arith (AddCarry 1 2 3 4) : 8 asm$inst) (fromAList [(4,())])``;
val _ = observe "carry_dead"
  ``remove_dead_inst (Arith (AddCarry 1 2 3 4) : 8 asm$inst) (LN)``;
val _ = observe "longmul_live"
  ``remove_dead_inst (Arith (LongMul 1 2 3 4) : 8 asm$inst) (fromAList [(2,())])``;
val _ = observe "to32"
  ``remove_dead_inst (FP (FPMovToReg 1 2 3) : 32 asm$inst) (fromAList [(2,())])``;
val _ = observe "to64"
  ``remove_dead_inst (FP (FPMovToReg 1 2 3) : 64 asm$inst) (fromAList [(2,())])``;
