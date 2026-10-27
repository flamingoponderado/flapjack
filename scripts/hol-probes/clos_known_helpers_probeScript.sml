load "clos_knownTheory"; load "clos_fvsTheory"; load "clos_ticksTheory"; load "clos_letopTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "fvs="; print_term (rhs (concl (EVAL ``
 clos_fvs$compile [closLang$Let None [closLang$Var None 0]
   (closLang$Fn «f» (SOME 4) (SOME [0;1]) 1 (closLang$Var None 3));
   closLang$Letrec [«f»] (SOME 4) (SOME [0]) [(1,closLang$Var None 3)] (closLang$Var None 1)]``))); print "\n");
val _ = (print "ticks="; print_term (rhs (concl (EVAL ``
 clos_ticks$remove_ticks [closLang$Tick None (closLang$Call None 7 4 [closLang$Tick None (closLang$Var None 0)]);
   closLang$Fn «f» (SOME 4) NONE 1 (closLang$Tick None (closLang$Var None 0))]``))); print "\n");
val _ = (print "letop="; print_term (rhs (concl (EVAL ``
 clos_letop$let_op [closLang$Let (SourceLoc 1 2 3 4) [closLang$Var None 2;closLang$Var None 3]
   (closLang$Op None (closLang$IntOp closLang$Add) [closLang$Var None 0;closLang$Var None 1])]``))); print "\n");
val _ = (print "decisions="; print_term (rhs (concl (EVAL ``
 let c = clos_known$mk_config 8 2 in
 let body = closLang$Op None (closLang$IntOp closLang$Add) [closLang$Var None 0;closLang$Var None 0] in
 [clos_known$get_size_sc 3 body; clos_known$get_size_sc 2 body] : num option list``))); print "\n");
val _ = (print "inline="; print_term (rhs (concl (EVAL ``
 let c = clos_known$mk_config 8 2 in
 let body = closLang$Op None (closLang$IntOp closLang$Add) [closLang$Var None 0;closLang$Var None 0] in
 [clos_known$decide_inline c (clos_known$Clos 4 1 body 3) NONE 1;
  clos_known$decide_inline c (clos_known$Clos 4 1 body 4) NONE 1;
  clos_known$decide_inline c (clos_known$ClosNoInline 4 1) NONE 1;
  clos_known$decide_inline c (clos_known$Clos 4 1 body 3) (SOME 9) 1;
  clos_known$decide_inline c (clos_known$Clos 4 1 (closLang$Var None 1) 1) NONE 1;
  clos_known$decide_inline c (clos_known$Clos 4 1 (closLang$Fn «x» NONE NONE 1 (closLang$Var None 0)) 1) NONE 1]``))); print "\n");
