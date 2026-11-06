load "bvl_constTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "divs="; print_term (rhs (concl (EVAL ``
 [(7:int) / 3; (-7:int) / 3; (7:int) / -3; (-7:int) / -3;
  (7:int) % 3; (-7:int) % 3; (7:int) % -3; (-7:int) % -3]``))); print "\n");
val _ = (print "ops="; print_term (rhs (concl (EVAL ``
 MAP (\(op,x,y). bvl_const$SmartOp op [x;y])
 [(closLang$IntOp closLang$Add, bvl$Var 0, bvl$Op (closLang$IntOp (closLang$Const 0)) []);
  (closLang$IntOp closLang$Sub, bvl$Op (closLang$IntOp (closLang$Const 7)) [], bvl$Op (closLang$IntOp (closLang$Const 3)) []);
  (closLang$IntOp closLang$Div, bvl$Op (closLang$IntOp (closLang$Const (-3))) [], bvl$Op (closLang$IntOp (closLang$Const 7)) []);
  (closLang$BlockOp closLang$Equal, bvl$Var 0, bvl$Op (closLang$IntOp (closLang$Const 4)) []);
  (closLang$MemOp closLang$El, bvl$Op (closLang$IntOp (closLang$Const 2)) [], bvl$Var 1)]``))); print "\n");
val _ = (print "compile="; print_term (rhs (concl (EVAL ``
 bvl_const$compile_exp (bvl$Let [bvl$Var 3; bvl$Op (closLang$IntOp (closLang$Const 5)) []]
   (bvl$Op (closLang$IntOp closLang$Add) [bvl$Var 0; bvl$Var 1]))``))); print "\n");
val _ = (print "algebra="; print_term (rhs (concl (EVAL ``
 let c = \i. bvl$Op (closLang$IntOp (closLang$Const i)) [] in
 let a = \x y. bvl$Op (closLang$IntOp closLang$Add) [x;y] in
 let s = \x y. bvl$Op (closLang$IntOp closLang$Sub) [x;y] in
 let m = \x y. bvl$Op (closLang$IntOp closLang$Mult) [x;y] in
 [bvl_const$SmartOp (closLang$IntOp closLang$Add) [a (bvl$Var 0) (c 2); c 3];
  bvl_const$SmartOp (closLang$IntOp closLang$Sub) [s (bvl$Var 0) (c 2); c 3];
  bvl_const$SmartOp (closLang$IntOp closLang$Add) [a (bvl$Var 0) (c 2); s (bvl$Var 1) (c 3)];
  bvl_const$SmartOp (closLang$IntOp closLang$Sub) [a (bvl$Var 0) (c 2); s (bvl$Var 1) (c 3)];
  bvl_const$SmartOp (closLang$IntOp closLang$Mult) [m (bvl$Var 0) (c 2); m (bvl$Var 1) (c 3)];
  bvl_const$SmartOp (closLang$IntOp closLang$Mod) [c (-3); c 7];
  bvl_const$SmartOp (closLang$IntOp closLang$Less) [c 3; c 2];
  bvl_const$SmartOp (closLang$BlockOp (closLang$EqualConst (closLang$Int 4))) [c 4]]``))); print "\n");
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "dest_simple=" bvl_constTheory.dest_simple_def;
val _ = show "case_op_const=" bvl_constTheory.case_op_const_def;
val _ = show "SmartOp_flip=" bvl_constTheory.SmartOp_flip_def;
val _ = show "SmartOp2=" bvl_constTheory.SmartOp2_def;
val _ = show "SmartOp1=" bvl_constTheory.SmartOp1_def;
val _ = show "SmartOp=" bvl_constTheory.SmartOp_def;
val _ = show "extract=" bvl_constTheory.extract_def;
val _ = show "extract_list=" bvl_constTheory.extract_list_def;
val _ = show "delete_var=" bvl_constTheory.delete_var_def;
val _ = show "compile_sing=" bvl_constTheory.compile_sing_def;
val _ = show "compile_eq=" bvl_constTheory.compile_eq;
val _ = show "compile_exp=" bvl_constTheory.compile_exp_def;
val _ = show "compile_exp_eq=" bvl_constTheory.compile_exp_eq;
