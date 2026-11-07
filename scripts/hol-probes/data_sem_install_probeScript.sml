load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "v_to_bytes=" dataSemTheory.v_to_bytes_def;
val _ = show "v_to_words=" dataSemTheory.v_to_words_def;
val _ = show "do_install=" dataSemTheory.do_install_def;
val _ = show "do_app=" dataSemTheory.do_app_def;
val _ = show "install_bad_arity=" (EVAL ``dataSem$do_install [] (s:('c,'ffi) dataSem$state)``);
val _ = show "greater_rejected=" (EVAL ``dataSem$do_app (closLang$IntOp closLang$Greater)
  [] (s:('c,'ffi) dataSem$state)``);
val _ = show "outer_install_bad_arity=" (EVAL ``dataSem$do_app closLang$Install
  [] (s:('c,'ffi) dataSem$state)``);
val _ = show "bytes_nil=" (EVAL ``dataSem$v_to_bytes (dataSem$Block 0 backend_common$nil_tag [])``);
val _ = show "words_nil=" (EVAL ``dataSem$v_to_words (dataSem$Block 0 backend_common$nil_tag [])``);
