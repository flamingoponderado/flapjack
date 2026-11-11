(* Typed source declarations for the constant definitions and datatypes in
   cakeml/semantics/semanticPrimitivesScript.sml. *)
load "preamble";
load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
open preamble semanticPrimitivesTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun showTerm label tm = (print (label ^ "="); print_term tm; print "\n");

val _ = show "bind_stamp_def_typed" semanticPrimitivesTheory.bind_stamp_def;
val _ = show "chr_stamp_def_typed" semanticPrimitivesTheory.chr_stamp_def;
val _ = show "div_stamp_def_typed" semanticPrimitivesTheory.div_stamp_def;
val _ = show "subscript_stamp_def_typed" semanticPrimitivesTheory.subscript_stamp_def;
val _ = show "bind_exn_v_def_typed" semanticPrimitivesTheory.bind_exn_v_def;
val _ = show "chr_exn_v_def_typed" semanticPrimitivesTheory.chr_exn_v_def;
val _ = show "div_exn_v_def_typed" semanticPrimitivesTheory.div_exn_v_def;
val _ = show "sub_exn_v_def_typed" semanticPrimitivesTheory.sub_exn_v_def;
val _ = show "exp_or_val_axiom_typed" semanticPrimitivesTheory.exp_or_val_Axiom;
val _ = showTerm "store_ffi_type_typed" (Term `\(x : ('v,'ffi) store_ffi). x`);
