load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "heterogeneous"
  ``let p = apply_nummaps_key (\n. n + 10)
      (fromAList [(1,T);(2,F)], fromAList [(3,7n);(4,8n)])
    in (toAList (FST p), toAList (SND p))``;
val _ = observe "collision"
  ``let p = apply_nummaps_key (\n. n MOD 2)
      (fromAList [(3,());(1,());(2,())], fromAList [(4,());(2,())])
    in (MAP FST (toAList (FST p)), MAP FST (toAList (SND p)))``;
val _ = observe "empty"
  ``let p = apply_nummaps_key (\n. n + 10)
      (LN:num_set, fromAList [(3,());(3,());(2,())])
    in (MAP FST (toAList (FST p)), MAP FST (toAList (SND p)))``;
