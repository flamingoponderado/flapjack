(* Typed source declarations for the remaining mlstring definitions (task 273). *)
load "preamble";
load "mlstringTheory";
open HolKernel Parse boolLib bossLib;
open preamble mlstringTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="mlstring",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by mlstring")
  | SOME (th,_) => show label th;

val _ = emit "fields_aux_def_typed" "fields_aux_def";
val _ = emit "fields_def_typed" "fields_def";
val _ = emit "fields_filter_typed" "fields_filter";
val _ = emit "fields_length_typed" "fields_length";
val _ = emit "isStringThere_aux_def_typed" "isStringThere_aux_def";
val _ = emit "isPrefix_def_typed" "isPrefix_def";
val _ = emit "isSuffix_def_typed" "isSuffix_def";
val _ = emit "isSubstring_aux_def_typed" "isSubstring_aux_def";
val _ = emit "isSubstring_def_typed" "isSubstring_def";
val _ = emit "isStringThere_SEG_typed" "isStringThere_SEG";
val _ = emit "isprefix_thm_typed" "isprefix_thm";
val _ = emit "exists_mlstring_typed" "exists_mlstring";
val _ = emit "strlit_STRCAT_typed" "strlit_STRCAT";
val _ = emit "substring_0_typed" "substring_0";
val _ = emit "str_findi_def_typed" "str_findi_def";
val _ = emit "str_findi_range_typed" "str_findi_range";
val _ = emit "substring_1_strsub_typed" "substring_1_strsub";
val _ = emit "substring_add_typed" "substring_add";
val _ = emit "isSubstring_aux_lemma_typed" "isSubstring_aux_lemma";
val _ = emit "isSubstring_SEG_typed" "isSubstring_SEG";
val _ = emit "isprefix_strcat_typed" "isprefix_strcat";
val _ = emit "char_lt_total_typed" "char_lt_total";
