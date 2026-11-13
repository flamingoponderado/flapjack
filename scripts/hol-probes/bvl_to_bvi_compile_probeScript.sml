load "bvl_to_bviTheory";
load "miscTheory";
open HolKernel Parse boolLib bossLib bvl_to_bviTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "smart_append_def=" miscTheory.SmartAppend_def;
val _ = show "compile_aux_def=" compile_aux_def;
val _ = show "compile_exps_sing_def=" compile_exps_sing_def;
val _ = show "compile_exps_sing=" compile_exps_sing;
val _ = show "compile_aux_example=" (EVAL ``compile_aux (2, T, bvi$Var 1)``);
val _ = show "compile_tree_example=" (EVAL ``compile_exps_sing 0
  (bvl$If (bvl$Let [] (bvl$Let [] (bvl$Var 0)))
    (bvl$Let [] (bvl$Let [] (bvl$Var 0)))
    (bvl$Let [] (bvl$Let [] (bvl$Var 0))))``);
val _ = show "compile_single_def=" compile_single_def;
val _ = show "compile_single_eq=" compile_single_eq;
val _ = show "compile_list_def=" compile_list_def;
val _ = show "compile_inc_def=" compile_inc_def;
val _ = show "compile_prog_def_typed=" compile_prog_def;
val _ = show "alloc_glob_count_def_typed=" alloc_glob_count_def;
val _ = show "alloc_glob_count_eq_global_count_list_typed=" alloc_glob_count_eq_global_count_list;
val _ = show "alloc_glob_count_empty=" (EVAL ``alloc_glob_count []``);
val _ = show "alloc_glob_count_nested=" (EVAL ``alloc_glob_count
  [bvl$Let [bvl$Op (closLang$GlobOp closLang$AllocGlobal) [];
            bvl$Raise (bvl$Op (closLang$GlobOp closLang$AllocGlobal) [])]
     (bvl$If (bvl$Var 0) (bvl$Tick (bvl$Op (closLang$GlobOp closLang$AllocGlobal) []))
       (bvl$Handle (bvl$Force 1 2)
         (bvl$Call 0 (SOME 0) [bvl$Op (closLang$GlobOp closLang$AllocGlobal) []])));
   bvl$Op (closLang$GlobOp (closLang$SetGlobal 0))
     [bvl$Op (closLang$GlobOp closLang$AllocGlobal) []]]``);
val _ = show "compile_inc_example=" (EVAL ``compile_inc 0
  [(1, 2, bvl$Let [] (bvl$Let [] (bvl$Var 0))); (2, 1, bvl$Var 0)]``);
val _ = Globals.show_types := false;
val _ = show "compile_inc_all_cache=" (EVAL ``
  let c = bvl_to_bvi$default_config with
    <| next_name1 := 2; next_name2 := 3; next_name3 := 4; do_tailrec := F; do_tmc := F |> in
  let (c, first) = bvl_to_bvi$bvl_to_bvi_compile_inc_all c [(1,1,bvl$Var 0)] in
  let (c, second) = bvl_to_bvi$bvl_to_bvi_compile_inc_all c
    [(2,1,bvl$Call 0 (SOME 1) [bvl$Var 0])] in
  (c.next_name1,c.next_name2,c.next_name3,toAList c.inlines,toAList c.bvi_inlines,first,second)``);
val _ = show "compile_inc_all_default=" (EVAL ``
  let (c, code) = bvl_to_bvi$bvl_to_bvi_compile_inc_all bvl_to_bvi$default_config
    [(1, 1, bvl$Var 0)] in
  (c.next_name1,c.next_name2,c.next_name3,toAList c.inlines,toAList c.bvi_inlines,code)``);
