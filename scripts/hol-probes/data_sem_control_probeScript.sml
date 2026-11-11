(* Typed source declarations for the clock and size facts in
   cakeml/compiler/backend/semantics/dataSemScript.sml. *)
load "preamble";
load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble dataSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun showTerm label tm = (print (label ^ "="); print_term tm; print "\n");

(* push_env_clock and pop_env_clock are [local] in the source theory, so replay
   their statements; do_stack_clock and vb_size_def are exported. *)
val _ = showTerm "push_env_clock_typed"
  (Term `∀(env :v sptree$num_map) (b :bool) (s :(α, β) dataSem$state).
     (dataSem$push_env env b s).clock = s.clock`);
val _ = showTerm "pop_env_clock_typed"
  (Term `∀(s :(α, β) dataSem$state) (s1 :(α, β) dataSem$state).
     (dataSem$pop_env s = SOME s1) ⇒ s1.clock = s.clock`);
val _ = show "do_stack_clock_typed" dataSemTheory.do_stack_clock;
val _ = show "vb_size_def_typed" dataSemTheory.vb_size_def;
