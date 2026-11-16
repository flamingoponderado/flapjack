load "backendPropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "state_orac_states_typed=" backendPropsTheory.state_orac_states_def;
val _ = show_thm "state_orac_states_inv_typed=" backendPropsTheory.state_orac_states_inv;
val _ = show_thm "oracle_monotonic_state_with_inv_init_typed=" backendPropsTheory.oracle_monotonic_state_with_inv_init;
val _ = show_thm "oracle_monotonic_state_typed=" backendPropsTheory.oracle_monotonic_state;
val _ = show_thm "oracle_monotonic_state_init_typed=" backendPropsTheory.oracle_monotonic_state_init;
val _ = show_thm "state_co_progs_typed=" backendPropsTheory.state_co_progs_def;
val _ = show_thm "add_state_co_typed=" backendPropsTheory.add_state_co_def;
val _ = show_thm "syntax_to_full_oracle_typed=" backendPropsTheory.syntax_to_full_oracle_def;
val _ = show_thm "state_oracle_example=" (EVAL
  ``(backendProps$state_orac_states (\s p. (2 * s + p, s + p)) 3 (\n. n + 1) 3,
     backendProps$state_co_progs (\s p. (2 * s + p, s + p)) 3 (\n. n + 1) 2,
     backendProps$add_state_co (\s p. (2 * s + p, s + p)) 3 (\xs i. xs i + 10) (\n. n + 1) 2)``);
val _ = show_thm "syntax_to_full_oracle_o_assoc_typed=" backendPropsTheory.syntax_to_full_oracle_o_assoc;
val _ = show_thm "FST_add_state_co_0_typed=" backendPropsTheory.FST_add_state_co_0;
val _ = show_thm "is_state_oracle_shift_imp_typed=" backendPropsTheory.is_state_oracle_shift_imp;
val _ = show_thm "is_state_oracle_add_state_co_typed=" backendPropsTheory.is_state_oracle_add_state_co;
val _ = show_thm "oracle_monotonic_step_typed=" backendPropsTheory.oracle_monotonic_step;
val _ = show_thm "oracle_monotonic_init_typed=" backendPropsTheory.oracle_monotonic_init;
val _ = show_thm "oracle_monotonic_step2_typed=" backendPropsTheory.oracle_monotonic_step2;
val _ = show_thm "oracle_monotonic_SND_syntax_to_full_typed=" backendPropsTheory.oracle_monotonic_SND_syntax_to_full;
val _ = show_thm "oracle_monotonic_shift_subset_typed=" backendPropsTheory.oracle_monotonic_shift_subset;
val _ = show_thm "is_state_oracle_shift_typed=" backendPropsTheory.is_state_oracle_shift;
val _ = show_thm "the_eqn_typed=" backendPropsTheory.the_eqn;
val _ = show_thm "the_F_eq_typed=" backendPropsTheory.the_F_eq;
val _ = show_thm "syntax_oracle_unpack_typed=" backendPropsTheory.syntax_oracle_unpack;
