load "clos_knownTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "merge="; print_term (rhs (concl (EVAL ``
 let f = closLang$Var None 0 in let h = closLang$Var None 1 in
 [clos_known$merge (clos_known$Clos 4 1 f 1) (clos_known$Clos 4 1 f 1);
  clos_known$merge (clos_known$Clos 4 1 f 1) (clos_known$Clos 4 1 h 1);
  clos_known$merge (clos_known$Tuple 2 [clos_known$Int 3;clos_known$Impossible]) (clos_known$Tuple 2 [clos_known$Int 3;clos_known$Int 5]);
  clos_known$merge (clos_known$Tuple 2 [clos_known$Int 3]) (clos_known$Tuple 3 [clos_known$Int 3])]``))); print "\n");
val _ = (print "knownop="; print_term (rhs (concl (EVAL ``
 let (a,g) = clos_known$known_op (closLang$GlobOp (closLang$SetGlobal 2)) [clos_known$Int 5] LN in
 let (b,g) = clos_known$known_op (closLang$GlobOp (closLang$Global 2)) [] g in
 let (c,g) = clos_known$known_op (closLang$MemOp closLang$El) [clos_known$Tuple 0 [clos_known$Int 8;clos_known$Int 9];clos_known$Int 1] g in
 (a,b,c,toAList g)``))); print "\n");
val _ = (print "compiled="; print_term (rhs (concl (EVAL ``
 let c = clos_known$mk_config 8 2 in
 let fn = closLang$Fn «f» (SOME 4) NONE 1 (closLang$Var None 0) in
 let input = [closLang$Let None [fn] (closLang$App None NONE (closLang$Var None 0) [closLang$Op None (closLang$IntOp (closLang$Const 42)) []]);
   closLang$Op None (closLang$GlobOp (closLang$SetGlobal 2)) [closLang$Op None (closLang$IntOp (closLang$Const 5)) []];
   closLang$Op None (closLang$GlobOp (closLang$Global 2)) []] in
 let (config,es) = clos_known$compile (SOME c) input in
 (es, toAList (clos_known$option_val_approx_spt config))``))); print "\n");
