load "clos_opTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "ops="; print_term (rhs (concl (EVAL ``
 let c = \i. closLang$Op None (closLang$IntOp (closLang$Const i)) [] in
 let cons = \tag xs. closLang$Op None (closLang$BlockOp (closLang$Cons tag)) xs in
 [clos_op$SmartOp (SourceLoc 1 2 3 4) (closLang$IntOp closLang$Div) [c (-3); c 7];
  clos_op$SmartOp None (closLang$IntOp closLang$Div) [c 0; c 7];
  clos_op$SmartOp None (closLang$BlockOp (closLang$ElemAt 0)) [cons 2 [closLang$Var None 0; closLang$Var None 1]];
  clos_op$SmartOp None (closLang$BlockOp (closLang$TagLenEq 2 2)) [cons 2 [closLang$Var None 0; closLang$Var None 1]];
  clos_op$SmartOp (SourceLoc 1 2 3 4) (closLang$BlockOp closLang$Equal) [closLang$Var None 0;closLang$Var None 1];
  clos_op$SmartOp None (closLang$BlockOp closLang$Equal) [c 2;closLang$Var None 0];
  clos_op$SmartOp None (closLang$BlockOp closLang$Equal) [cons 2 [];closLang$Var None 0];
  clos_op$SmartOp None (closLang$BlockOp closLang$Equal) [cons 2 [c 3;cons 4 []];closLang$Var None 5];
  clos_op$SmartOp None (closLang$BlockOp closLang$Equal) [cons 2 [closLang$Tick None (closLang$Var None 0)];cons 2 [closLang$Var None 1]];
  clos_op$SmartOp None (closLang$BlockOp closLang$Equal) [cons 2 [c 1];cons 3 [c 1]];
  clos_op$SmartOp None (closLang$BlockOp closLang$Equal) [cons 2 [c 1;c 2];cons 2 [c 1;c 3]];
  clos_op$SmartOp None (closLang$BlockOp closLang$Equal) [closLang$Var None 5;cons 2 [c 3;cons 4 []]]]``))); print "\n");
val _ = (print "signed="; print_term (rhs (concl (EVAL ``
 [clos_op$int_op (closLang$IntOp closLang$Div) 3 7;
  clos_op$int_op (closLang$IntOp closLang$Div) (-3) 7;
  clos_op$int_op (closLang$IntOp closLang$Div) 3 (-7);
  clos_op$int_op (closLang$IntOp closLang$Div) (-3) (-7);
  clos_op$int_op (closLang$IntOp closLang$Mod) 3 7;
  clos_op$int_op (closLang$IntOp closLang$Mod) (-3) 7;
  clos_op$int_op (closLang$IntOp closLang$Mod) 3 (-7);
  clos_op$int_op (closLang$IntOp closLang$Mod) (-3) (-7);
  clos_op$int_op (closLang$IntOp closLang$Div) 0 (-7);
  clos_op$int_op (closLang$IntOp closLang$Mod) 0 (-7)]``))); print "\n");
val _ = (print "lift="; print_term (rhs (concl (EVAL ``
 let c = \i. closLang$Op None (closLang$IntOp (closLang$Const i)) [] in
 let block = closLang$Op None (closLang$BlockOp (closLang$Cons 2))
   [closLang$Tick None (closLang$Var None 0); c 3] in
 (clos_op$lift_exps [] 2 [closLang$Var None 7],
  clos_op$lift_exps [block;closLang$Var None 4;c 5] 4 [closLang$Var None 7])``))); print "\n");
val _ = (print "eq_tree="; print_term (rhs (concl (EVAL ``
 let v = \i. closLang$Var None i in
 let c = \i. closLang$Op None (closLang$IntOp (closLang$Const i)) [] in
 let block = \tag xs. closLang$Op None (closLang$BlockOp (closLang$Cons tag)) xs in
 [clos_op$eq_pure_list [];
  clos_op$eq_pure_list [(v 0,v 1)];
  clos_op$eq_pure_list [(block 2 [c 3;v 0],v 1)];
  clos_op$eq_pure_list [(block 2 [v 0;v 1],block 2 [v 2;v 3])];
  clos_op$eq_pure_list [(block 2 [v 0],block 3 [v 1])];
  clos_op$eq_pure_list [(v 0,v 1);(c 4,v 2)]]``))); print "\n");
