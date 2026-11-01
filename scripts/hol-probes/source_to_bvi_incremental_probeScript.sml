(* Incremental source-to-BVI observations from the pinned original passes. *)
load "backendTheory";
open HolKernel Parse boolLib bossLib;
val _ = computeLib.add_funs [clos_to_bvlTheory.extract_name_pmatch];
val _ = Globals.linewidth := 1000000;
fun emit label tm =
  let val rewritten = rhs (concl (REWRITE_CONV
        [clos_to_bvlTheory.clos_to_bvl_compile_inc_def,
         clos_to_bvlTheory.compile_inc_def, clos_to_bvlTheory.extract_name_pmatch] tm))
  in (print (label ^ "="); print_term (rhs (concl (EVAL rewritten))); print "\n") end;

val _ = emit "source_incremental_empty" ``
  let sc = source_to_flat$empty_config in
  let cc = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 2; do_mti := F; do_call := F; known_conf := NONE |> in
  let bc = bvl_to_bvi$default_config with
    <| inline_size_limit := 0; do_tailrec := F; do_tmc := F |> in
  let (sc, flat) = source_to_flat$inc_compile (0,0) sc (source_to_source$compile []) in
  let clos = flat_to_clos$inc_compile_decs flat in
  let (cc, bvl) = clos_to_bvl$clos_to_bvl_compile_inc cc clos in
  let (bc, bvi) = bvl_to_bvi$bvl_to_bvi_compile_inc_all bc bvl in
  (sc.envs.next, sc.next.vidx, cc.next_loc, bc.next_name1, bc.next_name2, bc.next_name3, bvi)``;

val _ = emit "source_incremental_let" ``
  let sc = source_to_flat$empty_config in
  let cc = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 2; do_mti := F; do_call := F; known_conf := NONE |> in
  let bc = bvl_to_bvi$default_config with
    <| inline_size_limit := 0; do_tailrec := F; do_tmc := F |> in
  let ds = [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$Lit (ast$IntLit 1))] in
  let (sc, flat) = source_to_flat$inc_compile (0,0) sc (source_to_source$compile ds) in
  let clos = flat_to_clos$inc_compile_decs flat in
  let (cc, bvl) = clos_to_bvl$clos_to_bvl_compile_inc cc clos in
  let (bc, bvi) = bvl_to_bvi$bvl_to_bvi_compile_inc_all bc bvl in
  (sc.envs.next, sc.next.vidx, cc.next_loc, bc.next_name1, bc.next_name2, bc.next_name3, bvi)``;

val _ = emit "source_incremental_dependent" ``
  let sc = source_to_flat$empty_config in
  let cc = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 2; do_mti := F; do_call := F; known_conf := NONE |> in
  let bc = bvl_to_bvi$default_config with
    <| inline_size_limit := 0; do_tailrec := F; do_tmc := F |> in
  let ds1 = [ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$Lit (ast$IntLit 1))] in
  let (sc, flat1) = source_to_flat$inc_compile (0,0) sc (source_to_source$compile ds1) in
  let (cc, bvl1) = clos_to_bvl$clos_to_bvl_compile_inc cc (flat_to_clos$inc_compile_decs flat1) in
  let (bc, _) = bvl_to_bvi$bvl_to_bvi_compile_inc_all bc bvl1 in
  let ds2 = [ast$Dlet location$unknown_loc (ast$Pvar «y») (ast$Var (namespace$Short «x»))] in
  let (sc, flat2) = source_to_flat$inc_compile (0,0) sc (source_to_source$compile ds2) in
  let (cc, bvl2) = clos_to_bvl$clos_to_bvl_compile_inc cc (flat_to_clos$inc_compile_decs flat2) in
  let (bc, bvi2) = bvl_to_bvi$bvl_to_bvi_compile_inc_all bc bvl2 in
  (sc.envs.next, sc.next.vidx, cc.next_loc, bc.next_name1, bc.next_name2, bc.next_name3, bvi2)``;
