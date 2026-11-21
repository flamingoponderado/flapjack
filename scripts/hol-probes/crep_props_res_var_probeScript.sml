(* Typed source declarations for the crepProps res_var and locals-update lemmas
   (crepPropsScript.sml:234, :763, :796, :820, :203).  These captures support
   source review of the exact-carrier Lean twins; they do not establish
   HOL-to-Lean equivalence. *)
load "preamble";
load "crepPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble crepPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "res_var_commutes_typed" res_var_commutes;
val _ = show "flookup_res_var_distinct_eq_typed" flookup_res_var_distinct_eq;
val _ = show "flookup_res_var_distinct_typed" flookup_res_var_distinct;
val _ = show "flookup_res_var_zip_distinct_typed" flookup_res_var_zip_distinct;
val _ = show "update_locals_not_vars_eval_eq_pp_typed" update_locals_not_vars_eval_eq'';
val _ = (print "res_var_commutes_vars=";
  print (String.concatWith "," (map (fn t => fst (dest_var t))
    (Term.free_varsl [concl res_var_commutes])));
  print "\n");
