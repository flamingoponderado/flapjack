(* Typed source declarations for bvi_tailrecProofScript.sml. *)
load "preamble";
load "bvi_tailrecProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvi_tailrecProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "free_names_def_typed" bvi_tailrecProofTheory.free_names_def;
val _ = show "namespace_rel_def_typed" bvi_tailrecProofTheory.namespace_rel_def;
val _ = show "from_op_to_op_typed" bvi_tailrecProofTheory.from_op_to_op;
val _ = show "list_to_v_simp_typed" bvi_tailrecProofTheory.list_to_v_simp;
val _ = show "list_to_v_imp_typed" bvi_tailrecProofTheory.list_to_v_imp;
val _ = show "op_id_val_def_typed" bvi_tailrecProofTheory.op_id_val_def;
val _ = show "ty_rel_def_typed" bvi_tailrecProofTheory.ty_rel_def;
(* ty_rel_APPEND is [local] in the source theory, so replay its statement. *)
fun showTerm label tm = (print (label ^ "="); print_term tm; print "\n");
val _ = showTerm "ty_rel_APPEND_typed"
  (Term `∀(env :v list) (ts :v_ty list) (ws :v_ty list) (vs :v list).
     ty_rel env ts ∧ ty_rel vs ws ⇒ ty_rel (vs ++ env) (ws ++ ts)`);
val _ = show "ty_rel_decide_ty_typed" bvi_tailrecProofTheory.ty_rel_decide_ty;
