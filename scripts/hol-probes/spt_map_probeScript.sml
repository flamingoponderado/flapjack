load "bossLib";
load "preamble";
load "sptreeTheory";
open bossLib HolKernel Parse preamble sptreeTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "sm_empty" ``sptree$map (\x:num.x+1) LN = LN``;
val _ = observe "sm_leaf" ``sptree$map (\x:num.x+1) (LS 7) = LS 8``;
val _ = observe "sm_children" ``sptree$map (\x:num.x+1) (BN (LS 7) (LS 8)) = BN (LS 8) (LS 9)``;
val _ = observe "sm_root" ``sptree$map (\x:num.x+1) (BS (LS 7) 8 (LS 9)) = BS (LS 8) 9 (LS 10)``;
val _ = observe "sm_raw_bn" ``sptree$map (\x:num.x+1) (BN LN LN) = BN LN LN``;
val _ = observe "sm_raw_bs" ``sptree$map (\x:num.x+1) (BS LN 7 LN) = BS LN 8 LN``;
val _ = observe "sm_raw_nested" ``sptree$map (\x:num.x+1) (BS (BN LN LN) 7 (BS LN 8 LN)) = BS (BN LN LN) 8 (BS LN 9 LN)``;
val _ = observe "sm_bool_nat" ``sptree$map (\x:bool. if x then 1 else 0) (BS (LS F) T (LS T)) = BS (LS 0) 1 (LS 1)``;
val _ = observe "sm_nat_bool" ``sptree$map (\x:num. x=0) (BS (LS 7) 0 (LS 8)) = BS (LS F) T (LS F)``;
val _ = observe "sm_unit_raw" ``sptree$map (\x:num.()) (BS (BN LN LN) 7 (LS 8)) = BS (BN LN LN) () (LS ())``;
