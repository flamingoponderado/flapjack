(* Original stackSemScript.sml:743-747 optional stub code-shape guard. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;
val _ = observe "guard_none"
  ``check_store_consts_opt 4 5 NONE (ARB : 8 stackLang$prog sptree$num_map)``;
val _ = observe "guard_missing"
  ``check_store_consts_opt 4 5 (SOME 7) (LN : 8 stackLang$prog sptree$num_map)``;
val _ = observe "guard_match"
  ``check_store_consts_opt 4 5 (SOME 7)
    (insert 7 (Seq (StoreConsts 4 5 NONE) (Return 0) : 8 stackLang$prog) LN)``;
val _ = observe "guard_wrong_label"
  ``check_store_consts_opt 4 5 (SOME 8)
    (insert 7 (Seq (StoreConsts 4 5 NONE) (Return 0) : 8 stackLang$prog) LN)``;
val _ = observe "guard_wrong_first_register"
  ``check_store_consts_opt 4 5 (SOME 7)
    (insert 7 (Seq (StoreConsts 6 5 NONE) (Return 0) : 8 stackLang$prog) LN)``;
val _ = observe "guard_wrong_second_register"
  ``check_store_consts_opt 4 5 (SOME 7)
    (insert 7 (Seq (StoreConsts 4 6 NONE) (Return 0) : 8 stackLang$prog) LN)``;
val _ = observe "guard_recursive_stub"
  ``check_store_consts_opt 4 5 (SOME 7)
    (insert 7 (Seq (StoreConsts 4 5 (SOME 9)) (Return 0) : 8 stackLang$prog) LN)``;
val _ = observe "guard_return_nonzero"
  ``check_store_consts_opt 4 5 (SOME 7)
    (insert 7 (Seq (StoreConsts 4 5 NONE) (Return 1) : 8 stackLang$prog) LN)``;
val _ = observe "guard_wrong_constructor"
  ``check_store_consts_opt 4 5 (SOME 7)
    (insert 7 (StoreConsts 4 5 NONE : 8 stackLang$prog) LN)``;
val _ = observe "guard_reversed_sequence"
  ``check_store_consts_opt 4 5 (SOME 7)
    (insert 7 (Seq (Return 0) (StoreConsts 4 5 NONE) : 8 stackLang$prog) LN)``;
