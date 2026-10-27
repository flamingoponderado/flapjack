load "flat_patternTheory"; load "flat_elimTheory"; load "source_to_flatTheory"; load "flat_to_closTheory"; load "source_to_sourceTheory"; load "clos_to_bvlTheory"; load "bvl_to_bviTheory"; load "bvi_inlineTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "code="; print_term (rhs (concl (EVAL ``
 let (sc, flat) = source_to_flat$compile source_to_flat$empty_config (source_to_source$compile []) in
 let exps = flat_to_clos$compile_prog flat in
 let cc = clos_to_bvl$default_config with <| do_mti := F; do_call := F; known_conf := NONE; max_app := 0 |> in
 let (cc,bvl,names) = clos_to_bvl$compile cc exps in
 let (start,code,next) = bvl_to_bvi$compile_prog cc.start 0 bvl in
 SND (bvi_inline$compile_prog code)``))); print "\n");
