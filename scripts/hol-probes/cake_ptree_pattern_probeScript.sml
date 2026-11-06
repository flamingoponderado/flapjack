load "pegexec_cml_foTheory";
load "cmlPtreeConversionTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val listpat = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_fuel_fo 6000 (Nt_fo (INL nPattern) SemU_id)
 [(LbrackT,Locs (POSN 0 0) (POSN 0 1));
  (AlphaT «x»,Locs (POSN 0 1) (POSN 0 2));
  (CommaT,Locs (POSN 0 2) (POSN 0 3));
  (AlphaT «Ref»,Locs (POSN 0 4) (POSN 0 7));
  (AlphaT «y»,Locs (POSN 0 8) (POSN 0 9));
  (RbrackT,Locs (POSN 0 9) (POSN 0 10))] [] NONE [] Done_fo Failed_fo of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_Pattern nPattern pt
 | _ => NONE``));
val _ = (print "list="; print_term listpat; print "\n");
val typed = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_fuel_fo 6000 (Nt_fo (INL nPattern) SemU_id)
 [(AlphaT «x»,Locs (POSN 0 0) (POSN 0 1));
  (ColonT,Locs (POSN 0 2) (POSN 0 3));
  (AlphaT «int»,Locs (POSN 0 4) (POSN 0 7))] [] NONE [] Done_fo Failed_fo of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_Pattern nPattern pt
 | _ => NONE``));
val _ = (print "typed="; print_term typed; print "\n");
val literal = rhs (concl (EVAL ``
 (cmlPtreeConversion$ptree_Eliteral
    (Nd (INL nEliteral, unknown_loc) [Lf (TOK (WordT 42), unknown_loc)]),
  cmlPtreeConversion$ptree_Eliteral
    (Nd (INL nEliteral, unknown_loc) [Lf (TOK (FFIT «print»), unknown_loc)]) )``));
val _ = (print "literal="; print_term literal; print "\n");
