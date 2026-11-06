load "pegexec_cml_foTheory";
load "lexer_funTheory";
val _ = computeLib.add_funs [lexer_funTheory.get_token_def];
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val missing = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_core_fuel 30000 (lexer_fun$lexer_fun "val x = ;") of
   Result_fo (Success ((_,loc)::_) _ _) => SOME loc | _ => NONE``));
val _ = (print "missing="; print_term missing; print "\n");
val after_decl = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_core_fuel 30000 (lexer_fun$lexer_fun "val x = 1; val y = ;") of
   Result_fo (Success ((_,loc)::_) _ _) => SOME loc | _ => NONE``));
val _ = (print "after_decl="; print_term after_decl; print "\n");
val multiline = rhs (concl (EVAL ``
 case pegexec_cml_fo$peg_exec_core_fuel 30000 (lexer_fun$lexer_fun "val x = 1;\nval y = ;") of
   Result_fo (Success ((_,loc)::_) _ _) => SOME loc | _ => NONE``));
val _ = (print "multiline="; print_term multiline; print "\n");
