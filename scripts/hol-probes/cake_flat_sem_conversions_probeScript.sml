load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "v_to_list=" flatSemTheory.v_to_list_def;
val _ = show_thm "list_to_v=" flatSemTheory.list_to_v_def;
val _ = show_thm "v_to_char_list=" flatSemTheory.v_to_char_list_def;
val _ = show_thm "vs_to_string=" flatSemTheory.vs_to_string_def;
val _ = show_eval "empty_list=" ``flatSem$v_to_list (flatSem$list_to_v [])``;
val _ = show_eval "integer_list=" ``flatSem$v_to_list (flatSem$list_to_v [Litv (IntLit 1); Litv (IntLit 2)])``;
val _ = show_eval "bad_type=" ``flatSem$v_to_list (Conv (SOME (0, SOME 2)) [])``;
val _ = show_eval "bad_tail=" ``flatSem$v_to_list (Conv (SOME (0, SOME 1)) [Litv (IntLit 1); Litv (IntLit 2)])``;
val _ = show_eval "chars=" ``flatSem$v_to_char_list (flatSem$list_to_v [Litv (Char #"a"); Litv (Char #"b")])``;
val _ = show_eval "bad_char=" ``flatSem$v_to_char_list (flatSem$list_to_v [Litv (IntLit 1)])``;
val _ = show_eval "strings=" ``flatSem$vs_to_string [Litv (StrLit «ab»); Litv (StrLit «cd»)]``;
val _ = (print "bad_string="; print_term (rhs (concl (EVAL ``flatSem$vs_to_string [Litv (IntLit 1)]``))));
