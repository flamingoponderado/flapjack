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
