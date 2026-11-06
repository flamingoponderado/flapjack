load "lexer_implTheory"; load "lexer_funTheory";
val _ = computeLib.add_funs [lexer_funTheory.get_token_def];
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "chunks="; print_term (rhs (concl (EVAL ``
 lexer_impl$lex_impl_all_tokens (lexer_fun$lexer_fun "val x=1; let val y=2; in y end; val z=3")``))); print "\n");
