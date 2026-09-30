(* Direct original word_alloc get_live_exp, observed through mixed sptree traversal. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "nested" ``MAP FST (sptree$toAList (get_live_exp
  (Op Add [Const 7w; Load (Var 3); Lookup (Temp 9w); Shift Lsl (Var 5) (Var 6)] : 8 wordLang$exp)))``;
val _ = observe "duplicate" ``MAP FST (sptree$toAList (get_live_exp
  (Op Sub [Var 3; Var 3; Var 4] : 8 wordLang$exp)))``;
val _ = observe "empty" ``MAP FST (sptree$toAList (get_live_exp (Op Add [] : 8 wordLang$exp)))``;
val _ = observe "shift" ``MAP FST (sptree$toAList (get_live_exp
  (Shift Lsr (Var 0) (Op Add [Var 8; Var 1; Var 8]) : 8 wordLang$exp)))``;
val _ = observe "constant" ``MAP FST (sptree$toAList (get_live_exp (Const 255w : 8 wordLang$exp)))``;
val _ = observe "lookup" ``MAP FST (sptree$toAList (get_live_exp (Lookup (Temp 31w) : 8 wordLang$exp)))``;
