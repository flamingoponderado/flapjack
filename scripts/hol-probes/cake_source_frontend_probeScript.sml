load "pegexec_cml_foTheory";
load "cmlPtreeConversionTheory";
load "lexer_funTheory";
val _ = computeLib.add_funs [lexer_funTheory.get_token_def];
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val empty = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_core_fuel 5000 (lexer_fun$lexer_fun "") of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_TopLevelDecs pt
 | _ => NONE``));
val _ = (print "empty="; print_term empty; print "\n");
val value = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_core_fuel 30000 (lexer_fun$lexer_fun "val x = 1;") of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_TopLevelDecs pt
 | _ => NONE``));
val _ = (print "value="; print_term value; print "\n");
val dtypeResult = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_core_fuel 30000 (lexer_fun$lexer_fun "datatype t = A | B;") of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_TopLevelDecs pt
 | _ => NONE``));
val _ = (print "datatype="; print_term dtypeResult; print "\n");
val structureResult = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_core_fuel 30000 (lexer_fun$lexer_fun "structure M = struct val x = 1; end;") of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_TopLevelDecs pt
 | _ => NONE``));
val _ = (print "structure="; print_term structureResult; print "\n");
val exprResult = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_core_fuel 30000 (lexer_fun$lexer_fun "1;") of
  Result_fo (Success [] [pt] _) => cmlPtreeConversion$ptree_TopLevelDecs pt
 | _ => NONE``));
val _ = (print "expression="; print_term exprResult; print "\n");
