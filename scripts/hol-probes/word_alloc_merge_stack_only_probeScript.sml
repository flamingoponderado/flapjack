load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "mso_present_alloc" ``merge_stack_only (0,1) (LS (),LN) = (insert 1 () (LS ()),LS ())``;
val _ = observe "mso_present_physical" ``merge_stack_only (0,2) (LS (),LN) = (LS (),LN)``;
val _ = observe "mso_present_stack" ``merge_stack_only (0,3) (LS (),LN) = (LS (),LS ())``;
val _ = observe "mso_absent_stack_alloc" ``merge_stack_only (3,1) (LN,LN) = (insert 1 () LN,LN)``;
val _ = observe "mso_absent_stack_physical" ``merge_stack_only (3,2) (LN,LS ()) = (LN,LS ())``;
val _ = observe "mso_absent_delete_missing" ``merge_stack_only (2,1) (LS (),LN) = (LS (),LN)``;
val _ = observe "mso_absent_delete_root" ``merge_stack_only (2,0) (LS (),BN LN LN) = (LN,BN LN LN)``;
val _ = observe "mso_present_overwrite" ``merge_stack_only (0,5) (LS (),LS ()) = (insert 5 () (LS ()),LS ())``;
val _ = observe "mso_raw" ``merge_stack_only (2,0) (BN LN LN,BN LN LN) = (BN LN LN,BN LN LN)``;
