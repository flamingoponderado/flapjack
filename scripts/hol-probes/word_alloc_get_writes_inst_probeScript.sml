(* Direct original instruction-write observations; CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "writes_const"
  ``get_writes_inst (Const 1 (7w:8 word)) = sptree$insert 1 () sptree$LN``;
val _ = print_eval "writes_add_carry"
  ``get_writes_inst (Arith (AddCarry 1 2 3 4):8 inst) =
    sptree$insert 4 () (sptree$insert 1 () sptree$LN)``;
val _ = print_eval "writes_long_div"
  ``get_writes_inst (Arith (LongDiv 1 2 3 4 5):8 inst) =
    sptree$insert 2 () (sptree$insert 1 () sptree$LN)``;
val _ = print_eval "writes_load16_catchall"
  ``get_writes_inst (Mem Load16 1 (Addr 2 (0w:8 word))) = sptree$LN``;
val _ = print_eval "writes_fp_move64"
  ``get_writes_inst (FP (FPMovToReg 1 2 3):64 inst) = sptree$insert 1 () sptree$LN``;
val _ = print_eval "writes_fp_move32"
  ``get_writes_inst (FP (FPMovToReg 1 2 3):32 inst) =
    sptree$insert 2 () (sptree$insert 1 () sptree$LN)``;
val _ = print_eval "writes_fp_from_reg_catchall"
  ``get_writes_inst (FP (FPMovFromReg 3 1 2):32 inst) = sptree$LN``;
