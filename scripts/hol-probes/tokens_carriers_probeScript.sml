(* Typed source datatype axioms for cakeml/semantics/tokensScript.sml. *)
load "tokensTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "path_axiom_typed" tokensTheory.path_Axiom;
val _ = show "token_axiom_typed" tokensTheory.token_Axiom;
