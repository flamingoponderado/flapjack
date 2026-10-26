load "flat_patternTheory"; load "flat_elimTheory"; load "source_to_flatTheory"; load "flat_to_closTheory"; load "source_to_sourceTheory"; load "wordsLib";
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
val _ = capture "array_update" ``flat_to_clos$compile_op backend_common$None (flatLang$Src ast$Aupdate) [] =
  closLang$Let backend_common$None [] (closLang$If backend_common$None
    (closLang$Op backend_common$None (closLang$MemOp closLang$BoundsCheckArray) [closLang$Var backend_common$None 1; closLang$Var backend_common$None 2])
    (closLang$Op backend_common$None (closLang$MemOp closLang$Update) [closLang$Var backend_common$None 0; closLang$Var backend_common$None 1; closLang$Var backend_common$None 2])
    (closLang$Raise backend_common$None (closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 3)) [])))``;
val _ = capture "word8_conversion" ``flat_to_clos$compile_op backend_common$None (flatLang$Src (ast$FromTo ast$IntT (ast$WordT ast$W8))) [closLang$Var backend_common$None 7] =
  closLang$Op backend_common$None (closLang$IntOp closLang$Mod) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 256)) []; closLang$Var backend_common$None 7]``;
val _ = capture "compile_let" ``flat_to_clos$compile [] [flatLang$Let backend_common$None (SOME «x») (flatLang$Lit backend_common$None (ast$IntLit 4)) (flatLang$Var_local backend_common$None «x»)] =
  [closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 4)) []] (closLang$Var backend_common$None 0)]``;
val _ = capture "compile_constructor" ``flat_to_clos$compile [] [flatLang$Con backend_common$None (SOME (4, NONE)) [flatLang$Lit backend_common$None (ast$IntLit 1); flatLang$Lit backend_common$None (ast$IntLit 2)]] =
  [closLang$Op backend_common$None (closLang$BlockOp (closLang$Constant (closLang$ConstCons 4 [closLang$ConstInt 1; closLang$ConstInt 2]))) []]``;
val _ = capture "compile_nop" ``flat_to_clos$compile [] [flatLang$App backend_common$None (flatLang$Src (ast$FromTo ast$IntT (ast$WordT ast$W8))) [flatLang$App backend_common$None (flatLang$Src (ast$FromTo ast$CharT ast$IntT)) [flatLang$Lit backend_common$None (ast$IntLit 1)]]] =
  [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []]``;
val _ = capture "closure_empty_program" ``flat_to_clos$compile_prog [] = [clos_interp$compile_init F]``;
val _ = capture "closure_install_detect" ``closLang$has_install_list [closLang$Fn «f» NONE NONE 1 (closLang$Op backend_common$None closLang$Install [])]``;
val _ = capture "closure_init_false" ``clos_interp$compile_init F =
  closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$GlobOp closLang$AllocGlobal) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []]; closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []]
    (closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 0)) [closLang$Var backend_common$None 1])``;
val _ = capture "incremental_empty" ``flat_to_clos$inc_compile_decs [] =
  ([closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []], ([]:num list))``;
val _ = capture "interpreter_arity" ``[clos_interp$can_interpret_op (closLang$BlockOp (closLang$Cons 3)) 1; clos_interp$can_interpret_op (closLang$BlockOp (closLang$Cons 2)) 1]``;
val _ = capture "pattern_any_tree" ``pattern_comp$pats_to_code [(pattern_semantics$Any, 4); (pattern_semantics$Lit (ast$IntLit 3), 5)] = pattern_semantics$Leaf 4``;
val _ = capture "pattern_constructor_guard" ``pattern_comp$pat_to_guard [] (pattern_semantics$Cons (SOME (2, NONE)) [pattern_semantics$Lit (ast$IntLit 7)]) =
  pattern_semantics$Conj (pattern_semantics$PosTest pattern_common$EmptyPos (pattern_semantics$TagLenEq 2 1))
    (pattern_semantics$PosTest (pattern_common$Pos 0 pattern_common$EmptyPos) (pattern_semantics$LitEq (ast$IntLit 7)))``;
val _ = capture "pattern_nub" ``pattern_exh$ctor_nub [pattern_exh$TagC 1 0; pattern_exh$RefC; pattern_exh$TagC 1 0] = [pattern_exh$RefC; pattern_exh$TagC 1 0]``;
val _ = capture "pattern_specialize" ``pattern_exh$spec_row (pattern_exh$TagC 2 1) [pattern_semantics$Any; pattern_semantics$Lit (ast$IntLit 3)] = [[pattern_semantics$Any; pattern_semantics$Lit (ast$IntLit 3)]]``;
val _ = capture "pattern_compile_empty" ``pattern_comp$comp [] = pattern_semantics$Fail``;
val _ = capture "pattern_compile_any" ``pattern_comp$comp [(pattern_semantics$Any, 7)] = pattern_semantics$Leaf 7``;
val _ = capture "pattern_bind_variable" ``flat_pattern$compile_pat_rhs backend_common$None 0 (flatLang$Var_local backend_common$None «v») (flatLang$Pvar «x», flatLang$Lit backend_common$None (ast$IntLit 1)) =
  flatLang$Let backend_common$None (SOME «x») (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 1))``;
val _ = capture "pattern_compile_branch" ``flat_pattern$compile_pats (flat_pattern$init_config 0) F backend_common$None 0 (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 0)) [(flatLang$Pvar «x», flatLang$Lit backend_common$None (ast$IntLit 1))] =
  flatLang$Let backend_common$None (SOME «x») (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 1))``;
val _ = capture "empty_source_to_clos" ``(let (c, p) = source_to_flat$compile source_to_flat$empty_config [] in flat_to_clos$compile_prog p) =
 [closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$GlobOp closLang$AllocGlobal) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []]; closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []] (closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 0)) [closLang$Var backend_common$None 1]);
  closLang$Let (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) [closLang$Let (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) [] (closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$GlobOp closLang$AllocGlobal) [closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$IntOp (closLang$Const 1)) []])] (closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$BlockOp (closLang$Cons 0)) []);
  closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 1)) [closLang$Op backend_common$None (closLang$MemOp closLang$Ref) [closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []]]]``;
val _ = capture "reference_source_to_clos" ``(let (c,p) = source_to_flat$compile source_to_flat$empty_config [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$App ast$Opref [ast$Lit (ast$IntLit 1)])] in flat_to_clos$compile_prog p) =
 [closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$GlobOp closLang$AllocGlobal) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []]; closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []] (closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 0)) [closLang$Var backend_common$None 1]);
  closLang$Let (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) [closLang$Let (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) [] (closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$GlobOp closLang$AllocGlobal) [closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$IntOp (closLang$Const 2)) []])] (closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$BlockOp (closLang$Cons 0)) []);
  closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 1)) [closLang$Op backend_common$None (closLang$MemOp closLang$Ref) [closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []]];
  closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$MemOp closLang$Ref) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []]] (closLang$Let backend_common$None [closLang$Var backend_common$None 0] (closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 2)) [closLang$Var backend_common$None 0]))]``;
val _ = capture "source_let_lifting" ``source_to_source$compile [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$Let (SOME «y») (ast$Lit (ast$IntLit 1)) (ast$Var (namespace$Short «y»)))] =
 [ast$Dlocal [ast$Dlet location$unknown_loc (ast$Pvar «y») (ast$Lit (ast$IntLit 1))] [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$Var (namespace$Short «y»))]]``;
val _ = capture "lifted_source_to_clos" ``(let ds = source_to_source$compile [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$Let (SOME «y») (ast$App ast$Opref [ast$Lit (ast$IntLit 1)]) (ast$Var (namespace$Short «y»)))] in let (c,p) = source_to_flat$compile source_to_flat$empty_config ds in flat_to_clos$compile_prog p) =
  (let (c,p) = source_to_flat$compile source_to_flat$empty_config [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$App ast$Opref [ast$Lit (ast$IntLit 1)])] in flat_to_clos$compile_prog p)``;
