(* Direct observations of the pinned incremental closure-to-BVL compiler. *)
load "clos_to_bvlTheory";
open HolKernel Parse boolLib bossLib;
val _ = computeLib.add_funs [clos_to_bvlTheory.extract_name_pmatch];
val _ = Globals.linewidth := 1000000;
fun emit label tm =
  let val rewritten = rhs (concl (REWRITE_CONV
        [clos_to_bvlTheory.clos_to_bvl_compile_inc_def,
         clos_to_bvlTheory.compile_inc_def, clos_to_bvlTheory.extract_name_pmatch] tm))
  in (print (label ^ "="); print_term (rhs (concl (EVAL rewritten))); print "\n") end;

val _ = emit "incremental_aux" ``
  let c = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 2; do_mti := F; do_call := F; known_conf := NONE;
       call_state := (insert 9 () LN, [(3,0,closLang$Var None 0)]) |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c
    ([closLang$Var None 0], [(42,0,closLang$Var None 0)]) in
    (c'.next_loc, toAList (FST c'.call_state), SND c'.call_state, code)``;

val _ = emit "incremental_empty" ``
  let c = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 2; do_mti := F; do_call := F; known_conf := NONE |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c ([],[]) in
    (c'.next_loc, code)``;

val _ = emit "incremental_closure" ``
  let c = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 2; do_mti := F; do_call := F; known_conf := NONE |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c
    ([closLang$Fn «f» NONE NONE 1 (closLang$Var None 0)],[]) in
    (c'.next_loc, code)``;
