load "bvl_inlineTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "inline="; print_term (rhs (concl (EVAL ``
 SND (bvl_inline$tick_compile_prog 8 LN
   [(1,1,bvl$Var 0); (2,1,bvl$Call 2 (SOME 1) [bvl$Var 0]);
    (3,0,bvl$Call 0 (SOME 3) []); (4,1,bvl$Call 0 (SOME 3) [bvl$Var 0])])``))); print "\n");
val _ = (print "size="; print_term (rhs (concl (EVAL ``
 MAP (\n. bvl_inline$is_small_aux n [bvl$Let [bvl$Var 0; bvl$Tick (bvl$Var 1)] (bvl$Call 0 (SOME 4) [bvl$Var 0])]) [0;1;2;3;4]``))); print "\n");
val _ = (print "letop="; print_term (rhs (concl (EVAL ``
 bvl_inline$let_op_sing (bvl$Let [bvl$Var 8; bvl$Var 9]
   (bvl$Op (closLang$IntOp closLang$Add) [bvl$Var 0; bvl$Var 1]))``))); print "\n");
fun show_thm label th =
  if null (hyp th) then
    (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail ("hypotheses: " ^ label);
val _ = show_thm "optimise_def_typed=" bvl_inlineTheory.optimise_def;
val _ = show_thm "optimise_eq_typed=" bvl_inlineTheory.optimise_eq;
val _ = show_thm "compile_inc_def_typed=" bvl_inlineTheory.compile_inc_def;
val _ = show_thm "compile_prog_def_typed=" bvl_inlineTheory.compile_prog_def;
