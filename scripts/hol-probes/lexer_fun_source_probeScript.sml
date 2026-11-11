(* Typed source declarations for cakeml/semantics/lexer_funScript.sml. *)
load "preamble";
load "lexer_funTheory";
open HolKernel Parse boolLib bossLib;
open preamble lexer_funTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "symbol_axiom_typed" lexer_funTheory.symbol_Axiom;
val _ = show "next_loc_def_typed" lexer_funTheory.next_loc_def;
val _ = show "next_line_def_typed" lexer_funTheory.next_line_def;
val _ = show "get_token_def_typed" lexer_funTheory.get_token_def;
val _ = show "to_path_def_typed" lexer_funTheory.to_path_def;
val _ = show "token_of_sym_def_typed" lexer_funTheory.token_of_sym_def;
