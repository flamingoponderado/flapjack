load "clos_callTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "calls_sing_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.calls_sing_def); print "\n");
val _ = (print "calls_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.calls_def); print "\n");
val _ = (print "calls_sing_eq_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.calls_sing_eq); print "\n");
val _ = (print "compile_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.compile_def); print "\n");
val _ = (print "compile_inc_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.compile_inc_def); print "\n");
val _ = (print "cond_call_compile_inc_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.cond_call_compile_inc_def); print "\n");
val _ = (print "compile_eq_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.compile_eq); print "\n");
val _ = (print "compile_inc_eq_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.compile_inc_eq); print "\n");
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
val _ = (print "incremental="; print_term (rhs (concl (EVAL ``
 let p = ([closLang$Fn «f» (SOME 4) NONE 1 (closLang$Var None 0)],
          [(99,1,closLang$Var None 0)]) in
 let (set,(es,code)) = clos_call$compile_inc (insert 2 () LN) p in
 (toAList set,es,code)``))); print "\n");
val _ = (print "incremental_disabled="; print_term (rhs (concl (EVAL ``
 let p = ([closLang$Fn «f» (SOME 4) NONE 1 (closLang$Var None 0)],
          [(99,1,closLang$Var None 0)]) in
 let (set,(es,code)) = clos_call$cond_call_compile_inc F (insert 2 () LN) p in
 (toAList set,es,code)``))); print "\n");
