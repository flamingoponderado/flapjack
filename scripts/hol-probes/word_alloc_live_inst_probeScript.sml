load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "load16"
  ``MAP FST (toAList (get_live_inst (Mem Load16 3 (Addr 5 7w) : 8 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
val _ = observe "load8"
  ``MAP FST (toAList (get_live_inst (Mem Load8 3 (Addr 5 7w) : 8 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
val _ = observe "store32"
  ``MAP FST (toAList (get_live_inst (Mem Store32 3 (Addr 5 7w) : 8 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
val _ = observe "carry"
  ``MAP FST (toAList (get_live_inst (Arith (AddCarry 1 2 3 4) : 8 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
val _ = observe "overflow"
  ``MAP FST (toAList (get_live_inst (Arith (AddOverflow 1 2 3 4) : 8 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
val _ = observe "to64"
  ``MAP FST (toAList (get_live_inst (FP (FPMovToReg 1 2 3) : 64 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
val _ = observe "to32"
  ``MAP FST (toAList (get_live_inst (FP (FPMovToReg 1 2 3) : 32 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
val _ = observe "from64"
  ``MAP FST (toAList (get_live_inst (FP (FPMovFromReg 1 6 7) : 64 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
val _ = observe "from32"
  ``MAP FST (toAList (get_live_inst (FP (FPMovFromReg 1 6 7) : 32 asm$inst) (fromAList [(1,());(2,());(3,());(4,());(9,())])))``;
