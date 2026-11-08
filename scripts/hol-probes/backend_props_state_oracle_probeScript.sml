load "backendPropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "state_orac_states_typed=" backendPropsTheory.state_orac_states_def;
val _ = show_thm "state_orac_states_inv_typed=" backendPropsTheory.state_orac_states_inv;
val _ = show_thm "state_co_progs_typed=" backendPropsTheory.state_co_progs_def;
val _ = show_thm "add_state_co_typed=" backendPropsTheory.add_state_co_def;
val _ = show_thm "syntax_to_full_oracle_typed=" backendPropsTheory.syntax_to_full_oracle_def;
val _ = show_thm "state_oracle_example=" (EVAL
  ``(backendProps$state_orac_states (\s p. (2 * s + p, s + p)) 3 (\n. n + 1) 3,
     backendProps$state_co_progs (\s p. (2 * s + p, s + p)) 3 (\n. n + 1) 2,
     backendProps$add_state_co (\s p. (2 * s + p, s + p)) 3 (\xs i. xs i + 10) (\n. n + 1) 2)``);
