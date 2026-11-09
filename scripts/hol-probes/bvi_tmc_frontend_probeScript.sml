load "bvi_tmcTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "examples="; print_term (rhs (concl (EVAL ``
 let call = bvi$Call 2 (SOME 3) [bvi$Var 0] NONE in
 let cons = \xs. bvi$Op (closLang$BlockOp (closLang$Cons 0)) xs in
 MAP (bvi_tmc$compile_exp 3 59 1)
 [cons [bvi$Var 0; call];
  cons [call; bvi$Var 0];
  cons [bvi$Var 0; cons [bvi$Var 0; call]];
  cons [call; bvi$Call 0 (SOME 7) [] NONE];
  bvi$If (bvi$Var 0) (cons [bvi$Var 0; call]) (bvi$Var 0);
  bvi$Let [bvi$Var 0] (cons [bvi$Var 1; call]);
  cons [call; call];
  cons [bvi$Call 0 (SOME 7) [] NONE; call];
  cons [call; bvi$Op (closLang$IntOp (closLang$Const 268435458)) []]]``))); print "\n");
val _ = (print "program="; print_term (rhs (concl (EVAL ``
 let call = bvi$Call 2 (SOME 3) [bvi$Var 0] NONE in
 bvi_tmc$compile_prog T 59
 [(3,1,bvi$Op (closLang$BlockOp (closLang$Cons 0)) [bvi$Var 0; call]); (7,0,bvi$Var 0)]``))); print "\n");
