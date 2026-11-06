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

val _ = emit "incremental_mti_aux" ``
  let c = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 3; do_mti := T; do_call := F; known_conf := NONE |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c
    ([closLang$Fn «f» NONE NONE 1 (closLang$Fn «g» NONE NONE 1 (closLang$Var None 0))],
      [(42,0,closLang$Var None 0)]) in
    (c'.next_loc, code)``;

val _ = emit "incremental_mti_empty" ``
  let c = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 3; do_mti := T; do_call := F; known_conf := NONE |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c
    ([], [(42,0,closLang$Var None 0)]) in
    (c'.next_loc, code)``;

val _ = emit "incremental_call_closure" ``
  let c = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 2; do_mti := F; do_call := T; known_conf := NONE;
       call_state := (insert 9 () LN, [(3,0,closLang$Var None 0)]) |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c
    ([closLang$Fn «f» NONE NONE 1 (closLang$Var None 0)], [(42,0,closLang$Var None 0)]) in
    (c'.next_loc, toAList (FST c'.call_state), SND c'.call_state, code)``;

val _ = emit "incremental_call_mti" ``
  let c = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 3; do_mti := T; do_call := T; known_conf := NONE |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c
    ([closLang$Fn «f» NONE NONE 1 (closLang$Fn «g» NONE NONE 1 (closLang$Var None 0))], []) in
    (c'.next_loc, toAList (FST c'.call_state), code)``;

val _ = emit "incremental_known_globals" ``
  let k = (clos_known$default_config 2) with
    <| inline_factor := 0; val_approx_spt := insert 4 (clos_known$Int 7) LN |> in
  let c = clos_to_bvl$default_config with
    <| next_loc := 10; max_app := 2; do_mti := F; do_call := F; known_conf := SOME k |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c
    ([closLang$Op None (closLang$GlobOp (closLang$Global 4)) [];
      closLang$Op None (closLang$GlobOp (closLang$SetGlobal 5))
        [closLang$Op None (closLang$IntOp (closLang$Const 9)) []]],
      [(42,0,closLang$Var None 0)]) in
    (c'.next_loc, OPTION_MAP (\k. (k.inline_factor, toAList k.val_approx_spt)) c'.known_conf, code)``;

val _ = emit "incremental_known_default" ``
  let c = clos_to_bvl$default_config with <| next_loc := 10; max_app := 3 |> in
  let (c', code) = clos_to_bvl$clos_to_bvl_compile_inc c
    ([closLang$Fn «f» NONE NONE 1 (closLang$Fn «g» NONE NONE 1 (closLang$Var None 0))], []) in
    (c'.next_loc, toAList (FST c'.call_state),
      OPTION_MAP (\k. toAList k.val_approx_spt) c'.known_conf, code)``;
