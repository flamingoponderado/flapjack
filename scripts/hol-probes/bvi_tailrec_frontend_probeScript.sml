load "flat_patternTheory"; load "flat_elimTheory"; load "source_to_flatTheory"; load "flat_to_closTheory"; load "source_to_sourceTheory"; load "clos_to_bvlTheory"; load "bvl_inlineTheory"; load "bvl_to_bviTheory"; load "bvi_tailrecTheory"; load "bvi_tmcTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "decisions="; print_term (rhs (concl (EVAL ``
 let ds = [ast$Dlet location$unknown_loc (ast$Pvar «f») (ast$Fun «x» (ast$Fun «y» (ast$Var (namespace$Short «x»))))] in
 let (sc, flat) = source_to_flat$compile source_to_flat$empty_config (source_to_source$compile ds) in
 let exps = flat_to_clos$compile_prog flat in
 let cc = clos_to_bvl$default_config with <| do_mti := T; do_call := F; known_conf := NONE; max_app := 2 |> in
 let (cc,bvl,names) = clos_to_bvl$compile cc exps in
 let bvl = SND (bvl_inline$compile_prog 8 F 100 bvl) in
 let (start,code,next) = bvl_to_bvi$compile_prog cc.start 0 bvl in
 MAP (\(loc,arity,exp). (loc,bvi_tailrec$has_rec1 loc exp, IS_SOME (bvi_tailrec$check_exp loc arity exp))) code``))); print "\n");
val _ = (print "cases="; print_term (rhs (concl (EVAL ``
 MAP (bvi_tailrec$has_rec1 3)
 [bvi$Call 0 (SOME 3) [] NONE;
  bvi$Op (closLang$IntOp closLang$Add) [bvi$Call 0 (SOME 3) [] NONE; bvi$Var 0];
  bvi$Let [bvi$Op (closLang$IntOp closLang$Add) [bvi$Call 0 (SOME 3) [] NONE; bvi$Var 0]] (bvi$Var 0);
  bvi$If (bvi$Var 0) (bvi$Op (closLang$IntOp closLang$Add) [bvi$Call 0 (SOME 3) [] (SOME (bvi$Var 1)); bvi$Var 0]) (bvi$Var 1)]``))); print "\n");
val _ = (print "tmc="; print_term (rhs (concl (EVAL ``
 let ds = [ast$Dlet location$unknown_loc (ast$Pvar «f») (ast$Fun «x» (ast$Fun «y» (ast$Var (namespace$Short «x»))))] in
 let (sc, flat) = source_to_flat$compile source_to_flat$empty_config (source_to_source$compile ds) in
 let exps = flat_to_clos$compile_prog flat in
 let cc = clos_to_bvl$default_config with <| do_mti := T; do_call := F; known_conf := NONE; max_app := 2 |> in
 let (cc,bvl,names) = clos_to_bvl$compile cc exps in
 let bvl = SND (bvl_inline$compile_prog 8 F 100 bvl) in
 let (start,code,next) = bvl_to_bvi$compile_prog cc.start 0 bvl in
 MAP (\(loc,arity,exp). (loc, IS_SOME (bvi_tmc$compile_exp loc 59 arity exp))) code``))); print "\n");
