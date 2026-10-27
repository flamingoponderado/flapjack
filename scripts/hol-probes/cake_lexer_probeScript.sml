load "lexer_funTheory";
val _ = computeLib.add_funs [lexer_funTheory.get_token_def];
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "basic="; print_term (rhs (concl (EVAL ``
 lexer_fun$lexer_fun "val x = 0w10; Foo.Bar.< ~12"``))); print "\n");
val _ = (print "comments="; print_term (rhs (concl (EVAL ``
 lexer_fun$lexer_fun "(* a (* b *) *)\nlet x=0x2f in x end;"``))); print "\n");
val _ = (print "strings="; print_term (rhs (concl (EVAL ``
 lexer_fun$lexer_fun (MAP CHR [34;65;92;110;34;32;35;34;66;34;32;35;40;32;102;32;111;41])``))); print "\n");
val _ = (print "errors="; print_term (rhs (concl (EVAL ``
 MAP lexer_fun$lexer_fun ["0wz"; "*)"; "Foo."; "while _ 'a"; "\"unterminated"]``))); print "\n");
val _ = (print "edge="; print_term (rhs (concl (EVAL ``
 MAP lexer_fun$lexer_fun ["0x"; "0wx"; "0w"; "~9"; "A.B.+";
   MAP CHR [34;92;50;53;53;34]; MAP CHR [34;92;50;53;54;34]]``))); print "\n");
