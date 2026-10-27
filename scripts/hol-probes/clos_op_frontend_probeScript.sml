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
