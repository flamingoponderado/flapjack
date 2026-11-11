load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
val _ = show_type "globals_type=" ``λ(s:source_to_flatProof$global_env). s.v``;
val _ = show_type "constructors_type=" ``λ(s:source_to_flatProof$global_env). s.c``;
val _ = show_type "types_type=" ``λ(s:source_to_flatProof$global_env). s.tys``;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "has_bools=" source_to_flatProofTheory.has_bools_def;
val _ = show_thm "has_lists=" source_to_flatProofTheory.has_lists_def;
val _ = show_thm "has_exns=" source_to_flatProofTheory.has_exns_def;
val _ = show_thm "genv_c_ok=" source_to_flatProofTheory.genv_c_ok_def;
val _ = show_thm "genv_c_tys_ok=" source_to_flatProofTheory.genv_c_tys_ok_def;
val _ = show_thm "genv_lookup_nil=" source_to_flatProofTheory.genv_lookup_nil;
val _ = show_thm "genv_lookup_cons=" source_to_flatProofTheory.genv_lookup_cons;
val _ = show_thm "same_type_fst_same_ctor=" source_to_flatProofTheory.genv_c_ok_same_type_FST_eq_imp_same_ctor;
val _ = show_thm "pmatch_stamps_ok=" source_to_flatProofTheory.genv_c_ok_pmatch_stamps_ok;
val _ = show_thm "bind_tag=" backend_commonTheory.bind_tag_def;
val _ = show_thm "chr_tag=" backend_commonTheory.chr_tag_def;
val _ = show_thm "div_tag=" backend_commonTheory.div_tag_def;
val _ = show_thm "subscript_tag=" backend_commonTheory.subscript_tag_def;
val _ = show_thm "nil_tag=" backend_commonTheory.nil_tag_def;
val _ = show_thm "cons_tag=" backend_commonTheory.cons_tag_def;
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_eval "empty_bools=" ``source_to_flatProof$has_bools FEMPTY``;
val _ = show_eval "empty_lists=" ``source_to_flatProof$has_lists FEMPTY``;
val _ = show_eval "empty_exns=" ``source_to_flatProof$has_exns (FEMPTY : (num # bool option) # num |-> stamp)``;
val _ = (print "empty_types="; print_term (rhs (concl (EVAL ``source_to_flatProof$genv_c_tys_ok
  (FEMPTY : (num # bool option) # num |-> stamp) (FEMPTY : bool |-> (num # num) list)``))));
val _ = print "\n";

(* Replay the original local lookup/submap theorem with inferred carriers. *)
val flookup_funion_submap_replay = prove (
  ``(x ⊌ y) SUBMAP z ∧ FLOOKUP (x ⊌ y) k = SOME v ⇒ FLOOKUP z k = SOME v``,
  rw [finite_mapTheory.SUBMAP_DEF, finite_mapTheory.FLOOKUP_DEF] >> metis_tac []);
val _ = show_thm "flookup_funion_submap_typed=" flookup_funion_submap_replay;
val _ = show_thm "flookup_funion_submap_gen_all=" (GEN_ALL flookup_funion_submap_replay);

(* Replay the earlier local disjoint-union submap theorem. *)
val funion_submap_replay = prove (
  ``FUNION x y SUBMAP z ∧ DISJOINT (FDOM x) (FDOM y) ⇒ y SUBMAP z``,
  rw [finite_mapTheory.SUBMAP_DEF, pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION, finite_mapTheory.FUNION_DEF] >>
    metis_tac []);
val _ = show_thm "funion_submap_typed=" funion_submap_replay;
val _ = show_thm "funion_submap_gen_all=" (GEN_ALL funion_submap_replay);
