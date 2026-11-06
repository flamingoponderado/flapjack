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
