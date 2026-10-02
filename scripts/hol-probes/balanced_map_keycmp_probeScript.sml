load "balanced_mapTheory";
open HolKernel Parse bossLib balanced_mapTheory;
val _ = Globals.linewidth := 10000;
fun checked label th = (if null(hyp th) then () else raise Fail "open HOL hypotheses"; print(label ^ "="); print_thm th; print "\n");
val _ = checked "ksc_definition" key_set_cmp_def;
val _ = checked "ksc_full_theorem" key_set_cmp_thm;
val _ = checked "ksc_pair_definition" key_set_cmp2_def;
