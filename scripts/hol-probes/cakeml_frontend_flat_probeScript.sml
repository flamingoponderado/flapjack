load "flat_patternTheory"; load "flat_elimTheory"; load "source_to_flatTheory"; load "flat_to_closTheory"; load "wordsLib";
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
val word8_lit = EVAL ``flat_to_clos$compile_lit backend_common$None (ast$Word8 255w) = closLang$Op backend_common$None (closLang$IntOp (closLang$Const 255)) []``;
val _ = (print "word8_literal="; print_term (rhs (concl (CONV_RULE (RAND_CONV wordsLib.WORD_EVAL_CONV) word8_lit))); print "\n");
val _ = capture "smart_constructor" ``flat_to_clos$SmartCons backend_common$None 4 [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []; closLang$Op backend_common$None (closLang$IntOp (closLang$Const 2)) []] = closLang$Op backend_common$None (closLang$BlockOp (closLang$Constant (closLang$ConstCons 4 [closLang$ConstInt 2; closLang$ConstInt 1]))) []``;
val _ = capture "int_division" ``flat_to_clos$compile_arith backend_common$None ast$Div ast$IntT [] = closLang$Let backend_common$None [] (closLang$If backend_common$None (closLang$Op backend_common$None (closLang$BlockOp closLang$Equal) [closLang$Var backend_common$None 0; closLang$Op backend_common$None (closLang$IntOp (closLang$Const 0)) []]) (closLang$Raise backend_common$None (closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 2)) [])) (closLang$Op backend_common$None (closLang$IntOp closLang$Div) [closLang$Var backend_common$None 0; closLang$Var backend_common$None 1]))``;
val _ = capture "copy_string" ``flat_to_clos$CopyByteStr backend_common$None =
  closLang$If backend_common$None (closLang$Op backend_common$None (closLang$IntOp closLang$Less) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 0)) []; closLang$Var backend_common$None 0])
    (closLang$Raise backend_common$None (closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 3)) []))
    (closLang$If backend_common$None (closLang$Op backend_common$None (closLang$IntOp closLang$Less) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 0)) []; closLang$Var backend_common$None 1])
      (closLang$Raise backend_common$None (closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 3)) []))
      (closLang$If backend_common$None (closLang$Op backend_common$None (closLang$MemOp (closLang$BoundsCheckByte T)) [closLang$Op backend_common$None (closLang$IntOp closLang$Add) [closLang$Var backend_common$None 0; closLang$Var backend_common$None 1]; closLang$Var backend_common$None 2])
        (closLang$Op backend_common$None (closLang$MemOp (closLang$CopyByte T)) [closLang$Var backend_common$None 0; closLang$Var backend_common$None 1; closLang$Var backend_common$None 2])
        (closLang$Raise backend_common$None (closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 3)) []))))``;
