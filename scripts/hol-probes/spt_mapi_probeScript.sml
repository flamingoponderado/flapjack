load "bossLib";
load "preamble";
load "sptreeTheory";
open bossLib HolKernel Parse preamble sptreeTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "mi_empty" ``mapi (\k (x:num). k+x) LN = LN``;
val _ = observe "mi_leaf" ``mapi (\k (x:num). k+x) (LS 7) = LS 7``;
val _ = observe "mi_children" ``mapi (\k (x:num). (k,x)) (BN (LS 10) (LS 20)) = BN (LS (2,10)) (LS (1,20))``;
val _ = observe "mi_root" ``mapi (\k (x:num). (k,x)) (BS (LS 10) 30 (LS 20)) = BS (LS (2,10)) (0,30) (LS (1,20))``;
val _ = observe "mi_nested" ``mapi (\k (x:num). (k,x)) (BS (BS (LS 7) 8 (LS 9)) 10 (BN (LS 11) (LS 12))) = BS (BS (LS (6,7)) (2,8) (LS (4,9))) (0,10) (BN (LS (5,11)) (LS (3,12)))``;
val _ = observe "mi_raw_bn" ``mapi (\k (x:num). k+x) (BN LN LN) = LN``;
val _ = observe "mi_raw_bs" ``mapi (\k (x:num). k+x) (BS LN 7 LN) = LS 7``;
val _ = observe "mi_raw_nested" ``mapi (\k (x:num). (k,x)) (BS (BN LN LN) 7 (BS LN 8 LN)) = BS LN (0,7) (LS (1,8))``;
val _ = observe "mi_index3" ``mapi0 (\k (x:num). (k,x)) 3 (BS (LS 10) 30 (LS 20)) = BS (LS (11,10)) (3,30) (LS (7,20))``;
val _ = observe "mi_index6" ``mapi0 (\k (x:num). (k,x)) 6 (BN (LS 10) (LS 20)) = BN (LS (14,10)) (LS (10,20))``;
val _ = observe "mi_bool_nat" ``mapi (\k (x:bool). if x then k+100 else k) (BS (LS F) T (LS T)) = BS (LS 2) 100 (LS 101)``;
val _ = observe "mi_nat_bool" ``mapi (\k (x:num). k=x) (BS (LS 2) 0 (LS 9)) = BS (LS T) T (LS F)``;
