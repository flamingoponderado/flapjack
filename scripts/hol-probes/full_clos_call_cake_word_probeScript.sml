load "flat_patternTheory"; load "flat_elimTheory"; load "source_to_flatTheory"; load "flat_to_closTheory"; load "source_to_sourceTheory"; load "clos_to_bvlTheory"; load "bvl_inlineTheory"; load "bvl_to_bviTheory"; load "bvi_tailrecTheory"; load "bvi_tmcTheory"; load "bvi_to_dataTheory"; load "data_to_wordTheory"; load "bvi_inlineTheory"; load "wordsLib";
val _ = computeLib.add_funs [bvi_to_dataTheory.op_requires_names_eqn];
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val entry = EVAL ``
 let (sc, flat) = source_to_flat$compile source_to_flat$empty_config (source_to_source$compile [ast$Dlet location$unknown_loc (ast$Pvar «f») (ast$Fun «x» (ast$Fun «y» (ast$Var (namespace$Short «x»))))]) in
 let exps = flat_to_clos$compile_prog flat in
 let cc = clos_to_bvl$default_config with <| do_mti := T; do_call := T; known_conf := NONE; max_app := 2 |> in
 let (cc,bvl,names) = clos_to_bvl$compile cc exps in
 let bvl = SND (bvl_inline$compile_prog 8 F 100 bvl) in
 let (start,code,next) = bvl_to_bvi$compile_prog cc.start 0 bvl in
 let code = SND (bvi_tailrec$compile_prog T (backend_common$bvl_num_stubs + 2) code) in
 let code = SND (bvi_tmc$compile_prog T (backend_common$bvl_num_stubs + 3) code) in
 let code = SND (bvi_inline$compile_prog code) in
 let data = MAP bvi_to_data$compile_part code in
 let conf = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; call_empty_ffi := F; has_div := F; has_longdiv := F|> in
 let asm_conf = (ARB:64 asm$asm_config) with <| ISA := asm$RISC_V; fp_reg_count := 0 |> in
 MAP (\(loc, arity, body). (loc, arity, body, 0)) (data_to_word$compile_0 conf asm_conf data)``;
val _ = (print "entry="; print_term (rhs (concl (CONV_RULE
  (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.dimindex_64, wordsTheory.dimword_def] THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))) entry))); print "\n");
