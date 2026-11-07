load "clos_callTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "free="; print_term (rhs (concl (EVAL ``
 clos_call$free_sing (closLang$Fn «f» (SOME 4) NONE 1
   (closLang$Let None [closLang$Var None 3] (closLang$Var None 0)))``))); print "\n");
val _ = (print "closed="; print_term (rhs (concl (EVAL ``
 let (e,(set,code)) = clos_call$calls_sing
   (closLang$Fn «f» (SOME 4) NONE 1 (closLang$Var None 0)) (LN,[]) in
 (e,toAList set,code)``))); print "\n");
val _ = (print "open="; print_term (rhs (concl (EVAL ``
 let (e,(set,code)) = clos_call$calls_sing
   (closLang$Fn «f» (SOME 4) NONE 1 (closLang$Var None 2)) (LN,[]) in
 (e,toAList set,code)``))); print "\n");
val _ = (print "apps="; print_term (rhs (concl (EVAL ``
 let g = (insert 4 () LN,[]) in
 let (a,_) = clos_call$calls_sing (closLang$App None (SOME 4) (closLang$Var None 0) [closLang$Var None 1; closLang$Var None 2]) g in
 let (b,_) = clos_call$calls_sing (closLang$App None (SOME 4) (closLang$Tick None (closLang$Var None 0)) [closLang$Var None 1; closLang$Var None 2]) g in
 (a,b)``))); print "\n");
val _ = (print "letrec="; print_term (rhs (concl (EVAL ``
 let (e,(set,code)) = clos_call$calls_sing
   (closLang$Letrec [«f»;«g»] (SOME 10) NONE [(1,closLang$Var None 0);(1,closLang$Var None 0)] (closLang$Var None 0)) (LN,[]) in
 (e,toAList set,code)``))); print "\n");
