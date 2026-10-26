load "flat_patternTheory"; load "flat_elimTheory"; load "source_to_flatTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun capture label term =
  (print (label ^ "="); print_term (rhs (concl (EVAL term))); print "\n");

val _ = capture "name_roundtrips" ``MAP (flat_pattern$dec_name_to_num o flat_pattern$enc_num_to_name) [0; 89; 90; 181]``;
val _ = capture "name_bytes" ``MAP (MAP ORD o mlstring$explode o flat_pattern$enc_num_to_name) [0; 89; 90; 181]``;
val _ = capture "name_unreserved" ``flat_pattern$dec_name_to_num «x»``;
val _ = capture "pure_init" ``flat_elim$is_pure (flatLang$App backend_common$None (flatLang$GlobalVarInit 2) [flatLang$Lit backend_common$None (ast$IntLit 1)])``;
val _ = capture "hidden_init" ``flat_elim$is_hidden (flatLang$App backend_common$None (flatLang$GlobalVarInit 2) [flatLang$Lit backend_common$None (ast$IntLit 1)])``;
val _ = capture "impure_lookup_init" ``flat_elim$is_pure (flatLang$App backend_common$None (flatLang$GlobalVarInit 2) [flatLang$App backend_common$None (flatLang$GlobalVarLookup 1) []])``;
val _ = capture "hidden_lookup_init" ``flat_elim$is_hidden (flatLang$App backend_common$None (flatLang$GlobalVarInit 2) [flatLang$App backend_common$None (flatLang$GlobalVarLookup 1) []])``;
val _ = capture "keep_empty" ``flat_elim$keep sptree$LN (flatLang$App backend_common$None (flatLang$GlobalVarInit 2) [flatLang$Lit backend_common$None (ast$IntLit 1)])``;
val _ = capture "keep_reachable" ``flat_elim$keep (sptree$insert 2 () sptree$LN) (flatLang$App backend_common$None (flatLang$GlobalVarInit 2) [flatLang$Lit backend_common$None (ast$IntLit 1)])``;
val _ = capture "eliminate_pure_length" ``LENGTH (flat_elim$remove_flat_prog [flatLang$App backend_common$None (flatLang$GlobalVarInit 2) [flatLang$Lit backend_common$None (ast$IntLit 1)]])``;
val _ = capture "eval_bypass_length" ``LENGTH (flat_elim$remove_flat_prog [flatLang$App backend_common$None (flatLang$Src ast$Eval) []; flatLang$App backend_common$None (flatLang$GlobalVarInit 2) [flatLang$Lit backend_common$None (ast$IntLit 1)]])``;
val _ = capture "guard_double_not" ``flat_pattern$simp_guard (pattern_semantics$Not (pattern_semantics$Not pattern_semantics$True)) = pattern_semantics$True``;
val _ = capture "guard_false_conj" ``flat_pattern$simp_guard (pattern_semantics$Conj pattern_semantics$True (pattern_semantics$Not pattern_semantics$True)) = pattern_semantics$Not pattern_semantics$True``;
val _ = capture "pattern_encoding" ``flat_pattern$encode_pat (flatLang$Pcon (SOME (3, SOME (42, [(3, 1)]))) [flatLang$Pany]) = pattern_semantics$Cons (SOME (3, SOME [(3, 1)])) [pattern_semantics$Any]``;
val _ = capture "empty_program_globals" ``(FST (source_to_flat$compile_prog source_to_flat$empty_config [])).next.vidx``;
val _ = capture "empty_program_output" ``SND (source_to_flat$compile_prog source_to_flat$empty_config []) = [source_to_flat$glob_alloc ((FST (source_to_flat$compile_prog source_to_flat$empty_config [])).next) source_to_flat$empty_config; source_to_flat$alloc_env_ref]``;
