load "pegexec_cml_foTheory";
load "cmlPtreeConversionTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val funexpr = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_fuel_fo 12000 (Nt_fo (INL nE) SemU_id)
 [(FnT,Locs (POSN 0 0) (POSN 0 2));
  (AlphaT «x»,Locs (POSN 0 3) (POSN 0 4));
  (DarrowT,Locs (POSN 0 5) (POSN 0 7));
  (AlphaT «x»,Locs (POSN 0 8) (POSN 0 9))] [] NONE [] Done_fo Failed_fo of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_Expr nE pt
 | _ => NONE``));
val _ = (print "function="; print_term funexpr; print "\n");
val let_expr = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_fuel_fo 16000 (Nt_fo (INL nE) SemU_id)
 [(LetT,Locs (POSN 0 0) (POSN 0 3));
  (ValT,Locs (POSN 0 4) (POSN 0 7));
  (AlphaT «x»,Locs (POSN 0 8) (POSN 0 9));
  (EqualsT,Locs (POSN 0 10) (POSN 0 11));
  (IntT 1,Locs (POSN 0 12) (POSN 0 13));
  (InT,Locs (POSN 0 14) (POSN 0 16));
  (AlphaT «x»,Locs (POSN 0 17) (POSN 0 18));
  (SymbolT «+»,Locs (POSN 0 19) (POSN 0 20));
  (IntT 2,Locs (POSN 0 21) (POSN 0 22));
  (EndT,Locs (POSN 0 23) (POSN 0 26))] [] NONE [] Done_fo Failed_fo of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_Expr nE pt
 | _ => NONE``));
val _ = (print "let="; print_term let_expr; print "\n");
val case_expr = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_fuel_fo 16000 (Nt_fo (INL nE) SemU_id)
 [(CaseT,Locs (POSN 0 0) (POSN 0 4));
  (AlphaT «x»,Locs (POSN 0 5) (POSN 0 6));
  (OfT,Locs (POSN 0 7) (POSN 0 9));
  (AlphaT «y»,Locs (POSN 0 10) (POSN 0 11));
  (DarrowT,Locs (POSN 0 12) (POSN 0 14));
  (AlphaT «y»,Locs (POSN 0 15) (POSN 0 16))] [] NONE [] Done_fo Failed_fo of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_Expr nE pt
 | _ => NONE``));
val _ = (print "case="; print_term case_expr; print "\n");
