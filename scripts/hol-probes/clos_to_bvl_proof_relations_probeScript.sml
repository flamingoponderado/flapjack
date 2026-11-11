(* Typed source declarations for the relation and oracle lemmas in
   cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml. *)
load "preamble";
load "clos_to_bvlProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble clos_to_bvlProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun showTerm label tm = (print (label ^ "="); print_term tm; print "\n");

val _ = show "global_table_def_typed" clos_to_bvlProofTheory.global_table_def;
val _ = show "ref_rel_def_typed" clos_to_bvlProofTheory.ref_rel_def;
val _ = show "ref_rel_simp_typed" clos_to_bvlProofTheory.ref_rel_simp;
val _ = show "nth_code_def_typed" clos_to_bvlProofTheory.nth_code_def;
val _ = show "compile_oracle_inv_def_typed" clos_to_bvlProofTheory.compile_oracle_inv_def;
val _ = show "closure_code_installed_subspt_typed" clos_to_bvlProofTheory.closure_code_installed_subspt;
(* compile_exps_IMP_code_installed is [local], so replay its statement. *)
val _ = showTerm "compile_exps_IMP_code_installed_typed"
  (Term `∀(max_app :num) (xs :closLang$exp list) (aux :(num # num # bvl$exp) list)
     (c :bvl$exp list) (aux1 :(num # num # bvl$exp) list) (code :(num # bvl$exp) num_map).
     (compile_exps max_app xs aux = (c,aux1)) ∧ code_installed aux1 code ⇒ code_installed aux code`);
