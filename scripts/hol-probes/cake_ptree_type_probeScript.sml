load "pegexec_cml_foTheory";
load "cmlPtreeConversionTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val result = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_fuel_fo 5000 (Nt_fo (INL nType) SemU_id)
 [(TyvarT «'a»,Locs (POSN 0 0) (POSN 0 2));
  (ArrowT,Locs (POSN 0 3) (POSN 0 5));
  (AlphaT «int»,Locs (POSN 0 6) (POSN 0 9));
  (AlphaT «list»,Locs (POSN 0 10) (POSN 0 14))] [] NONE [] Done_fo Failed_fo of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_Type nType pt
 | _ => NONE``));
val _ = (print "type="; print_term result; print "\n");
val abbrev = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_fuel_fo 5000 (Nt_fo (INL nTypeAbbrevDec) SemU_id)
 [(TypeT,Locs (POSN 0 0) (POSN 0 4));
  (TyvarT «'a»,Locs (POSN 0 5) (POSN 0 7));
  (AlphaT «box»,Locs (POSN 0 8) (POSN 0 11));
  (EqualsT,Locs (POSN 0 12) (POSN 0 13));
  (TyvarT «'a»,Locs (POSN 0 14) (POSN 0 16));
  (AlphaT «list»,Locs (POSN 0 17) (POSN 0 21))] [] NONE [] Done_fo Failed_fo of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_TypeAbbrevDec pt
 | _ => NONE``));
val _ = (print "abbrev="; print_term abbrev; print "\n");
