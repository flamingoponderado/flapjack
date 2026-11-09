load "pegexec_cml_foTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "unary="; print_term (rhs (concl (EVAL ``
 pegexec_cml_fo$eval_unary (SemU_bindNT (INL nE))
  [Lf (TOK (IntT 1),Locs (POSN 0 1) (POSN 0 2)); Lf (TOK (IntT 2),Locs (POSN 0 4) (POSN 0 5))]``))); print "\n");
val _ = (print "infix="; print_term (rhs (concl (EVAL ``
 let a = Lf (TOK (IntT 1),Locs (POSN 0 1) (POSN 0 2)) in
 let op = Lf (TOK (SymbolT «+»),Locs (POSN 0 3) (POSN 0 4)) in
 let b = Lf (TOK (IntT 2),Locs (POSN 0 5) (POSN 0 6)) in
 pegexec_cml_fo$eval_binary (SemB_mklinfix (INL nEadd)) [a] [op;b]``))); print "\n");
val _ = (print "actions="; print_term (rhs (concl (EVAL ``
 let a = Lf (TOK (IntT 1),Locs (POSN 0 1) (POSN 0 2)) in
 let b = Lf (TOK (IntT 2),Locs (POSN 0 5) (POSN 0 6)) in
 let comma = Lf (TOK CommaT,Locs (POSN 0 3) (POSN 0 4)) in
 [pegexec_cml_fo$eval_binary SemB_foldl_Eapp [a] [b];
  pegexec_cml_fo$eval_binary SemB_foldl_DType [a] [b];
  pegexec_cml_fo$eval_binary SemB_papp_ctor_rpt [a] [b];
  pegexec_cml_fo$eval_binary SemB_ebase_paren_apply [a;b;comma;b;a] []]``))); print "\n");
