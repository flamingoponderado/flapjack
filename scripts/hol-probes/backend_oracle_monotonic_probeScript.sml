load "backendPropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "state_co=" backendPropsTheory.state_co_def;
val _ = show "oracle_monotonic=" backendPropsTheory.oracle_monotonic_def;
val _ = show "is_state_oracle=" backendPropsTheory.is_state_oracle_def;
val _ = show "monotonic_with_invariant=" backendPropsTheory.oracle_monotonic_state_with_inv;
