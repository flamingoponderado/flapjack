load "flat_patternTheory"; load "flat_elimTheory"; load "source_to_flatTheory"; load "flat_to_closTheory"; load "source_to_sourceTheory"; load "clos_to_bvlTheory"; load "bvl_to_bviTheory"; load "bvi_to_dataTheory"; load "data_to_wordTheory"; load "wordsLib";
val _ = computeLib.add_funs [bvi_to_dataTheory.op_requires_names_eqn];
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val entry = EVAL ``
 let (sc, flat) = source_to_flat$compile source_to_flat$empty_config (source_to_source$compile [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$App ast$Opref [ast$Lit (ast$IntLit 1)])]) in
 let exps = flat_to_clos$compile_prog flat in
 let cc = clos_to_bvl$default_config with <| do_mti := F; do_call := F; known_conf := NONE; max_app := 0 |> in
 let (cc,bvl,names) = clos_to_bvl$compile cc exps in
 let (start,code,next) = bvl_to_bvi$compile_prog cc.start 0 bvl in
 let data = MAP bvi_to_data$compile_part code in
 let conf = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; call_empty_ffi := F|> in
 MAP (\(loc, arity, body). (loc, arity, data_to_word$comp conf loc 2 body : 64 wordLang$prog # num))
   (FILTER (\(loc, arity, body). loc = 92) data)``;
val _ = (print "entry="; print_term (rhs (concl (CONV_RULE
  (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.dimindex_64, wordsTheory.dimword_def] THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))) entry))); print "\n");
