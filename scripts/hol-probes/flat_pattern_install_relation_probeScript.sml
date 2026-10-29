load "flat_patternProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "pure_cc=" backendPropsTheory.pure_cc_def;
val _ = show_thm "pure_co=" backendPropsTheory.pure_co_def;
val _ = show_thm "snd_pure_co=" backendPropsTheory.SND_pure_co;
val _ = show_thm "fst_pure_co=" backendPropsTheory.FST_pure_co;
val _ = show_thm "pure_co_comp=" backendPropsTheory.pure_co_comb_pure_co;
val _ = show_thm "pure_co_id=" backendPropsTheory.pure_co_I;
val _ = show_thm "pure_cc_id=" backendPropsTheory.pure_cc_I;
val _ = show_thm "install_relation=" flat_patternProofTheory.install_conf_rel_def;
val _ = show_thm "decs_semantics=" flat_patternProofTheory.compile_decs_semantics;
