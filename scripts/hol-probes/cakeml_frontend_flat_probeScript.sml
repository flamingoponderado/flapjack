load "flat_patternTheory"; load "flat_elimTheory"; load "source_to_flatTheory"; load "flat_to_closTheory"; load "source_to_sourceTheory"; load "clos_to_bvlTheory"; load "clos_numberTheory"; load "bvl_to_bviTheory"; load "bvi_letTheory"; load "dataLangTheory"; load "data_spaceTheory"; load "data_simpTheory"; load "data_liveTheory"; load "bvi_to_dataTheory"; load "data_to_wordTheory"; load "wordsLib";
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
val _ = capture "pattern_exhaustive" ``[pattern_exh$exh_rows ([]:(pattern_semantics$pat # num) list); pattern_exh$exh_rows [(pattern_semantics$Any, 0)]; pattern_exh$exh_rows [(pattern_semantics$Lit (ast$IntLit 1), 0)]; pattern_exh$exh_rows [(pattern_semantics$Cons (SOME (0, SOME [(0,0);(1,0)])) [], 0); (pattern_semantics$Cons (SOME (1, SOME [(0,0);(1,0)])) [], 1)]]``;
val _ = capture "pattern_bind_variable" ``flat_pattern$compile_pat_rhs backend_common$None 0 (flatLang$Var_local backend_common$None «v») (flatLang$Pvar «x», flatLang$Lit backend_common$None (ast$IntLit 1)) =
  flatLang$Let backend_common$None (SOME «x») (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 1))``;
val _ = capture "pattern_compile_branch" ``flat_pattern$compile_pats (flat_pattern$init_config 0) F backend_common$None 0 (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 0)) [(flatLang$Pvar «x», flatLang$Lit backend_common$None (ast$IntLit 1))] =
  flatLang$Let backend_common$None (SOME «x») (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 1))``;
val _ = capture "pattern_naive_branch" ``flat_pattern$compile_pats (flat_pattern$init_config 0) T backend_common$None 0 (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 0)) [(flatLang$Pvar «x», flatLang$Lit backend_common$None (ast$IntLit 1))] =
  flatLang$Let backend_common$None (SOME «x») (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 1))``;
val _ = capture "pattern_constructor_branch" ``flat_pattern$compile_pats (flat_pattern$init_config 0) F backend_common$None 0 (flatLang$Var_local backend_common$None «v») (flatLang$Lit backend_common$None (ast$IntLit 0)) [(flatLang$Pcon (SOME (2, NONE)) [flatLang$Pvar «x»], flatLang$Var_local backend_common$None «x»)] =
  flatLang$If backend_common$None (flatLang$App backend_common$None (flatLang$TagLenEq 2 1) [flatLang$Var_local backend_common$None «v»]) (flatLang$Let backend_common$None (SOME «..%») (flatLang$App backend_common$None (flatLang$El 0) [flatLang$Var_local backend_common$None «v»]) (flatLang$Let backend_common$None (SOME «x») (flatLang$Var_local backend_common$None «..%») (flatLang$Var_local backend_common$None «x»))) (flatLang$Lit backend_common$None (ast$IntLit 0))``;
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
val _ = capture "match_source_to_clos" ``(let ds = source_to_source$compile [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$App ast$Opref [ast$Mat (ast$Lit (ast$IntLit 1)) [(ast$Plit (ast$IntLit 1), ast$Lit (ast$IntLit 2)); (ast$Pany, ast$Lit (ast$IntLit 3))]])] in let (c,p) = source_to_flat$compile source_to_flat$empty_config ds in flat_to_clos$compile_prog p) =
 [closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$GlobOp closLang$AllocGlobal) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []]; closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []] (closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 0)) [closLang$Var backend_common$None 1]);
  closLang$Let (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) [closLang$Let (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) [] (closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$GlobOp closLang$AllocGlobal) [closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$IntOp (closLang$Const 2)) []])] (closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$BlockOp (closLang$Cons 0)) []);
  closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 1)) [closLang$Op backend_common$None (closLang$MemOp closLang$Ref) [closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []]];
  closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$MemOp closLang$Ref) [closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []] (closLang$If backend_common$None (closLang$Op backend_common$None (closLang$BlockOp closLang$Equal) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []; closLang$Var backend_common$None 0]) (closLang$Op backend_common$None (closLang$IntOp (closLang$Const 2)) []) (closLang$Op backend_common$None (closLang$IntOp (closLang$Const 3)) []))]] (closLang$Let backend_common$None [closLang$Var backend_common$None 0] (closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 2)) [closLang$Var backend_common$None 0]))]``;
val _ = capture "match_bind_source_to_clos" ``(let ds = source_to_source$compile [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$App ast$Opref [ast$Mat (ast$Lit (ast$IntLit 1)) [(ast$Pvar «y», ast$Var (namespace$Short «y»))]])] in let (c,p) = source_to_flat$compile source_to_flat$empty_config ds in flat_to_clos$compile_prog p) =
 [closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$GlobOp closLang$AllocGlobal) [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []]; closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []] (closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 0)) [closLang$Var backend_common$None 1]);
  closLang$Let (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) [closLang$Let (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) [] (closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$GlobOp closLang$AllocGlobal) [closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$IntOp (closLang$Const 2)) []])] (closLang$Op (backend_common$Cons (backend_common$SourceLoc 2 2 1 1) 1) (closLang$BlockOp (closLang$Cons 0)) []);
  closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 1)) [closLang$Op backend_common$None (closLang$MemOp closLang$Ref) [closLang$Op backend_common$None (closLang$BlockOp (closLang$Cons 0)) []]];
  closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$MemOp closLang$Ref) [closLang$Let backend_common$None [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 1)) []] (closLang$Let backend_common$None [closLang$Var backend_common$None 0] (closLang$Var backend_common$None 0))]] (closLang$Let backend_common$None [closLang$Var backend_common$None 0] (closLang$Op backend_common$None (closLang$GlobOp (closLang$SetGlobal 2)) [closLang$Var backend_common$None 0]))]``;
val _ = capture "bvl_shared_constant" ``clos_to_bvl$compile_const (closLang$ConstCons 30 [closLang$ConstInt 1; closLang$ConstInt 1]) = closLang$BlockOp (closLang$Build [closLang$Int 1; closLang$Con 32 [0; 0]])``;
val _ = capture "bvl_stub_layout" ``[clos_to_bvl$num_stubs 4; clos_to_bvl$partial_app_fn_location 4 3 1]``;
val _ = capture "bvl_chain_empty" ``clos_to_bvl$chain_exps 7 [] = [(7, 0, closLang$Op backend_common$None (closLang$IntOp (closLang$Const 0)) [])]``;
val _ = capture "bvl_code_sort" ``clos_to_bvl$code_sort [(1,10); (1,20); (1,30); (0,40)] = [(0,40); (1,20); (1,30); (1,10)]``;
val _ = capture "bvl_build_aux" ``clos_to_bvl$build_aux 3 [(1,bvl$Var 0); (2,bvl$Var 1)] [] = (7, [(5,2,bvl$Var 1); (3,1,bvl$Var 0)])``;
val _ = capture "bvl_source_names" ``let names = clos_to_bvl$get_src_names [closLang$Fn «first» (SOME 0) NONE 1 (closLang$Var backend_common$None 0); closLang$Fn «last» (SOME 0) NONE 1 (closLang$Var backend_common$None 0)] sptree$LN in [sptree$lookup 0 names; sptree$lookup 1 names] = [SOME «last_clos»; SOME «last»]``;

val _ = capture "closure_numbering" ``clos_number$renumber_code_locs 4 (closLang$Fn «f» NONE NONE 1 (closLang$Fn «g» NONE NONE 1 (closLang$Var backend_common$None 0))) =
 (8, closLang$Fn «f» (SOME 6) NONE 1 (closLang$Fn «g» (SOME 4) NONE 1 (closLang$Var backend_common$None 0)))``;
val _ = capture "closure_number_incremental" ``clos_number$compile_inc 3 [closLang$Fn «f» NONE NONE 1 (closLang$Var backend_common$None 0)] =
 (6, [closLang$Op backend_common$None (closLang$IntOp (closLang$Const 3)) []; closLang$Fn «f» (SOME 4) NONE 1 (closLang$Var backend_common$None 0)])``;
val _ = capture "bvl_closure_call" ``clos_to_bvl$mk_cl_call (bvl$Var 2) [bvl$Var 1; bvl$Var 0] =
 bvl$If (bvl$Op (closLang$BlockOp (closLang$EqualConst (closLang$Int 1))) [bvl$Op (closLang$BlockOp (closLang$ElemAt 1)) [bvl$Var 2]])
  (bvl$Call 1 NONE [bvl$Var 1; bvl$Var 0; bvl$Var 2; bvl$Op (closLang$BlockOp (closLang$ElemAt 0)) [bvl$Var 2]])
  (bvl$Call 0 (SOME 1) [bvl$Var 1; bvl$Var 0; bvl$Var 2])``;
val _ = capture "bvl_partial_application" ``clos_to_bvl$generate_partial_app_closure_fn 2 1 =
 bvl$Let [bvl$Op (closLang$BlockOp (closLang$ElemAt 2)) [bvl$Var 1]]
  (bvl$Call 0 NONE [bvl$Var 1; bvl$Op (closLang$BlockOp (closLang$ElemAt 3)) [bvl$Var 2]; bvl$Op (closLang$BlockOp (closLang$ElemAt 4)) [bvl$Var 2]; bvl$Var 0; bvl$Op (closLang$BlockOp (closLang$ElemAt 0)) [bvl$Var 0]])``;
fun captureExtract label term =
  let val rewritten = rhs (concl (REWRITE_CONV [clos_to_bvlTheory.extract_name_pmatch] term))
  in capture label rewritten end;
val _ = captureExtract "bvl_extract_name" ``
 let x = closLang$Op backend_common$None (closLang$IntOp (closLang$Const 7)) [] in
 let neg = closLang$Op backend_common$None (closLang$IntOp (closLang$Const (-1))) [] in
 clos_to_bvl$extract_name [x; closLang$Var backend_common$None 2] = (7, [closLang$Var backend_common$None 2]) /\
 clos_to_bvl$extract_name [x] = (7, [x]) /\
 clos_to_bvl$extract_name [neg; closLang$Var backend_common$None 2] = (0, [neg; closLang$Var backend_common$None 2])``;
val _ = capture "bvl_name_alist" ``let names = clos_to_bvl$make_name_alist [0; 2; 3; 4; 5; 6; 7] [(0, 0, closLang$Fn «f» (SOME 0) NONE 1 (closLang$Var backend_common$None 0))] 4 2 1 in
 MAP (\n. sptree$lookup n names) [0; 2; 3; 4; 5; 6; 7] = [SOME «bvl_stub»; SOME «bvl_force»; SOME «bvl_init»; SOME «f_clos»; SOME «f»; SOME «dec»; SOME «unknown_clos_fun»]``;
val _ = capture "bvl_recursive_closures" ``
 clos_to_bvl$recc_Lets 4 [1; 2] 2 (bvl$Var 0) = bvl$Let [clos_to_bvl$recc_Let 6 1 1] (bvl$Let [clos_to_bvl$recc_Let 4 2 0] (bvl$Var 0)) /\
 clos_to_bvl$recc_Let0 6 1 1 = bvl$Let [bvl$Op (closLang$BlockOp (closLang$Cons 30)) [bvl$Var 0; bvl$Op (closLang$IntOp (closLang$Const 0)) []; bvl$Op (closLang$Label 6) []]]
  (bvl$Let [bvl$Op (closLang$MemOp closLang$Update) [bvl$Var 0; bvl$Op (closLang$IntOp (closLang$Const 1)) []; bvl$Var 1]] (bvl$Var 1)) /\
 clos_to_bvl$build_recc_lets [1;2] [5] 4 2 (bvl$Var 0) =
  bvl$Let [bvl$Let [bvl$Op (closLang$MemOp closLang$Ref) [bvl$Var 5; bvl$Op (closLang$IntOp (closLang$Const 0)) []; bvl$Op (closLang$IntOp (closLang$Const 0)) []]] (clos_to_bvl$recc_Let0 6 2 1)]
   (bvl$Let [clos_to_bvl$recc_Let 4 1 0] (bvl$Var 0))``;
val _ = capture "bvl_compile_closure" ``clos_to_bvl$compile_exp_sing 0
 (closLang$Fn «f» (SOME 3) (SOME [2]) 1 (closLang$Var backend_common$None 0)) [] =
 (bvl$Op (closLang$BlockOp (closLang$Cons 30)) [bvl$Var 2; bvl$Op (closLang$IntOp (closLang$Const 0)) []; bvl$Op (closLang$Label 5) []],
  [(5, 2, bvl$Let [bvl$Var 0; bvl$Op (closLang$BlockOp (closLang$ElemAt 2)) [bvl$Var 1]] (bvl$Var 0))])``;
val _ = capture "bvl_compile_program" ``clos_to_bvl$compile_prog 0
 [(10, 0, closLang$Var backend_common$None 0); (8, 1, closLang$Fn «f» (SOME 3) (SOME [2]) 1 (closLang$Var backend_common$None 0))] =
 [(12, 0, bvl$Var 0);
  (10, 1, bvl$Op (closLang$BlockOp (closLang$Cons 30)) [bvl$Var 2; bvl$Op (closLang$IntOp (closLang$Const 0)) []; bvl$Op (closLang$Label 5) []]);
  (5, 2, bvl$Let [bvl$Var 0; bvl$Op (closLang$BlockOp (closLang$ElemAt 2)) [bvl$Var 1]] (bvl$Var 0))]``;
val _ = capture "bvl_to_bvi_analysis" ``
 bvl_to_bvi$compile_int 268435457 = bvi$Op (closLang$IntOp (closLang$Const 268435457)) [] /\
 bvl_to_bvi$compile_int 268435458 = bvi$Op (closLang$BlockOp (closLang$Build [closLang$Int 268435458])) [] /\
 bvl_to_bvi$compile_int (-268435458) = bvi$Op (closLang$BlockOp (closLang$Build [closLang$Int (-268435458)])) [] /\
 bvl_to_bvi$global_count_sing (bvl$Let [bvl$Op (closLang$GlobOp closLang$AllocGlobal) []; bvl$Raise (bvl$Op (closLang$GlobOp closLang$AllocGlobal) [])] (bvl$Op (closLang$GlobOp closLang$AllocGlobal) [])) = 3``;
val _ = capture "bvl_to_bvi_operations" ``
 bvl_to_bvi$compile_op (closLang$IntOp (closLang$Const 9)) [bvi$Var 1] = bvi$Let [bvi$Op (closLang$IntOp (closLang$Const 0)) [bvi$Var 1]] (bvi$Op (closLang$IntOp (closLang$Const 9)) []) /\
 bvl_to_bvi$compile_op (closLang$GlobOp (closLang$SetGlobal 4)) [bvi$Var 2] = bvi$Op (closLang$GlobOp (closLang$SetGlobal 5)) [bvi$Var 2] /\
 bvl_to_bvi$compile_op (closLang$MemOp (closLang$CopyByte T)) [] =
  bvi$Let [bvi$Op (closLang$IntOp (closLang$Const 0)) []; bvi$Op (closLang$IntOp (closLang$Const 0)) []; bvi$Op (closLang$IntOp (closLang$Const 0)) []]
   (bvi$Let [bvi$Op (closLang$MemOp (closLang$RefByte T)) [bvi$Op (closLang$IntOp (closLang$Const 0)) []; bvi$Var 0]]
    (bvi$Let [bvi$Op (closLang$MemOp (closLang$CopyByte F)) [bvi$Op (closLang$IntOp (closLang$Const 0)) []; bvi$Var 0; bvi$Var 1; bvi$Var 2; bvi$Var 3]] (bvi$Var 1)))``;
val _ = capture "bvi_let_optimization" ``
 bvi_let$extract_list [bvi$Var 2; bvi$Op (closLang$IntOp (closLang$Const 7)) []] = [4; 0] /\
 bvi_let$compile_sing [] 0 (bvi$Let [bvi$Var 2; bvi$Op (closLang$IntOp (closLang$Const 7)) []] (bvi$Var 0)) =
  bvi$Let [bvi$Op (closLang$IntOp (closLang$Const 0)) []; bvi$Op (closLang$IntOp (closLang$Const 7)) []] (bvi$Var 4) /\
 bvi_let$compile_sing [] 0 (bvi$Let [bvi$Var 2; bvi$Op (closLang$IntOp (closLang$Const 7)) []] (bvi$Var 1)) =
  bvi$Let [bvi$Var 2] (bvi$Op (closLang$IntOp (closLang$Const 7)) [])``;
val _ = capture "bvl_to_bvi_marker" ``bvl_to_bvi$compile_exps_sing 0
 (bvl$Let [] (bvl$Let [bvl$Var 2] (bvl$Var 0))) =
 (bvi$Call 0 (SOME (backend_common$bvl_num_stubs + 1)) [bvi$Var 2] NONE,
  bvl_to_bvi$compile_aux (0, 1, bvi$Var 0), 1)``;
val _ = capture "bvl_to_bvi_incremental" ``bvl_to_bvi$compile_inc 0 [(5, 1, bvl$Var 0)] =
 (0, [(backend_common$bvl_num_stubs + 20, 1, bvi$Var 0)])``;
val _ = capture "clos_to_bvi_program" ``bvl_to_bvi$compile_inc 0
 (clos_to_bvl$compile_prog 0 [(10, 0, closLang$Var backend_common$None 0)]) =
 (0, [(backend_common$bvl_num_stubs + 48, 0, bvi$Var 0)])``;
fun captureData label term =
  let val rewritten = rhs (concl (REWRITE_CONV [bvi_to_dataTheory.iAssign_def, bvi_to_dataTheory.op_requires_names_eqn] term))
  in capture label rewritten end;
val _ = captureData "data_lang_syntax" ``
 dataLang$op_space_reset (closLang$MemOp (closLang$CopyByte T)) /\
 ~dataLang$op_space_reset (closLang$MemOp (closLang$CopyByte F)) /\
 dataLang$op_requires_names (closLang$MemOp (closLang$CopyByte F)) /\
 ~dataLang$op_requires_names (closLang$IntOp (closLang$Const 1)) /\
 dataLang$mk_ticks 2 dataLang$Skip = dataLang$Seq dataLang$Tick (dataLang$Seq dataLang$Tick dataLang$Skip)``;
val _ = capture "data_space_requirements" ``
 data_space$num_size 4294967296 = 3 /\
 data_space$part_space_req (closLang$Int 536870911) = 0 /\
 data_space$part_space_req (closLang$Int (-536870912)) = 2 /\
 data_space$part_space_req (closLang$Str «abcde») = 3 /\
 data_space$op_space_req (closLang$BlockOp (closLang$Cons 4)) 2 = 3 /\
 data_space$op_space_req (closLang$WordOp (closLang$WordFromWord F)) 0 = 3``;
val _ = captureData "bvi_to_data_assign" ``
 bvi_to_data$iAssign 4 (closLang$IntOp closLang$Greater) [1;2] [3] [] =
  dataLang$Assign 4 (closLang$IntOp closLang$Less) [2;1] (SOME (sptree$list_to_num_set [1;2;3])) /\
 bvi_to_data$iAssign 0 (closLang$WordOp (closLang$WordTest ast$W8 (ast$Compare ast$Gt))) [1;2] [] [] =
  dataLang$Assign 0 (closLang$WordOp (closLang$WordTest ast$W8 (ast$Compare ast$Lt))) [2;1] NONE /\
 bvi_to_data$iAssign 0 (closLang$MemOp closLang$Ref) [1;2] [] [] =
  dataLang$Seq (dataLang$MakeSpace 3 (sptree$list_to_num_set [1;2])) (dataLang$Assign 0 (closLang$MemOp closLang$Ref) [1;2] NONE)``;
fun captureBviData label term =
  let val rewritten = rhs (concl (REWRITE_CONV [bvi_to_dataTheory.compile_sing_def,
        bvi_to_dataTheory.iAssign_def, bvi_to_dataTheory.op_requires_names_eqn] term))
  in capture label rewritten end;
val _ = captureBviData "bvi_to_data_expression" ``bvi_to_data$compile_sing 0 [5] T []
 (bvi$Op (closLang$IntOp (closLang$Const 4)) [bvi$Var 0]) =
 (dataLang$Seq (dataLang$Seq dataLang$Skip (dataLang$Assign 6 (closLang$IntOp (closLang$Const 4)) [5] NONE))
   (dataLang$Return [6]), 6, 7)``;
val _ = capture "data_simplification" ``
 data_simp$simp (dataLang$Seq (dataLang$Move 1 2) (dataLang$Return [1])) (dataLang$Move 3 4) =
  dataLang$Seq (dataLang$Move 1 2) (dataLang$Return [1]) /\
 data_simp$simp (dataLang$If 0 (dataLang$Seq dataLang$Skip (dataLang$Raise 1)) dataLang$Skip) dataLang$Skip =
  dataLang$If 0 (dataLang$Raise 1) dataLang$Skip``;
val _ = capture "data_liveness" ``
 data_live$compile (dataLang$Seq (dataLang$Assign 1 (closLang$IntOp (closLang$Const 3)) [0] NONE) (dataLang$Return [0])) sptree$LN =
  (dataLang$Seq dataLang$Skip (dataLang$Return [0]), sptree$list_insert [0] sptree$LN) /\
 data_live$compile (dataLang$Seq (dataLang$Assign 1 (closLang$IntOp closLang$Add) [0;2] NONE) (dataLang$Return [0])) sptree$LN =
  (dataLang$Seq (dataLang$Assign 1 (closLang$IntOp closLang$Add) [0;2] NONE) (dataLang$Return [0]), sptree$list_insert [0;2] (sptree$list_insert [0] sptree$LN))``;
val _ = capture "data_optimisation" ``
 data_space$compile (dataLang$Seq (dataLang$Assign 0 (closLang$MemOp closLang$Ref) [1] NONE) (dataLang$MakeSpace 3 sptree$LN)) =
  dataLang$Seq (dataLang$MakeSpace 5 (sptree$list_insert [1] sptree$LN))
   (dataLang$Seq (dataLang$Assign 0 (closLang$MemOp closLang$Ref) [1] NONE) dataLang$Skip) /\
 bvi_to_data$optimise (dataLang$Seq (dataLang$Assign 1 (closLang$IntOp (closLang$Const 3)) [0] NONE) (dataLang$Return [0])) = dataLang$Return [0]``;
val _ = capture "bvi_to_data_complete_example" ``bvi_to_data$compile_exp 1 (bvi$Var 0) = dataLang$Return [0]``;
val _ = capture "clos_to_data_program" ``
 MAP (\(name, args, exp). (name, args, bvi_to_data$compile_exp args exp))
  (SND (bvl_to_bvi$compile_inc 0 (clos_to_bvl$compile_prog 0 [(10, 1, closLang$Var backend_common$None 0)]))) =
 [(backend_common$bvl_num_stubs + 48, 1, dataLang$Return [0])]``;
val _ = capture "data_to_word_variables" ``
 data_to_word$adjust_var 7 = 16 /\
 let names = data_to_word$adjust_set (sptree$insert 1 8 (sptree$insert 0 9 sptree$LN)) in
 [sptree$lookup 0 names; sptree$lookup 2 names; sptree$lookup 4 names] = [NONE; SOME (); SOME ()]``;
val header_test = EVAL ``let conf = (ARB:data_to_word$config) with len_size := 4 in
 data_to_word$encode_header conf 3 5 = SOME (0x500000000000000Fw:word64) /\
 data_to_word$encode_header conf 3 5 = SOME (0x5000000Fw:word32) /\
 data_to_word$encode_header conf 3 16 = (NONE:word64 option)``;
val _ = (print "data_to_word_header="; print_term (rhs (concl (CONV_RULE (RAND_CONV wordsLib.WORD_EVAL_CONV) header_test))); print "\n");

val _ = capture "data_to_word_locations" ``[data_to_word$FromList_location; data_to_word$FromList1_location; data_to_word$RefByte_location; data_to_word$RefArray_location; data_to_word$Replicate_location; data_to_word$AnyArith_location; data_to_word$Add_location; data_to_word$Sub_location; data_to_word$Mul_location; data_to_word$Div_location; data_to_word$Mod_location; data_to_word$Compare1_location; data_to_word$Compare_location; data_to_word$Equal1_location; data_to_word$Equal_location; data_to_word$LongDiv1_location; data_to_word$LongDiv_location; data_to_word$MemCopy_location; data_to_word$ByteCopy_location; data_to_word$ByteCopyAdd_location; data_to_word$ByteCopySub_location; data_to_word$ByteCopyNew_location; data_to_word$Install_location; data_to_word$InstallCode_location; data_to_word$InstallData_location; data_to_word$Dummy_location; data_to_word$Append_location; data_to_word$AppendMainLoop_location; data_to_word$AppendLenLoop_location; data_to_word$XorLoop_location; data_to_word$Unused_location; data_to_word$StringCmpLoop_location; data_to_word$Bignum_location] = GENLIST (\n. n + 7) 33``;
