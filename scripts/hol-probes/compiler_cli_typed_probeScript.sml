(* Typed captures for the self-contained `cakeml` driver helpers in
   compilerScript.sml (task 273): flag tests, mlstring printing and parsing
   helpers, and the line/column utilities. The configuration parsers are not
   captured here because they need the full `config` record. *)
load "preamble";
load "compilerTheory";
open HolKernel Parse boolLib bossLib;
open preamble compilerTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "compiler", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in compiler>\n");

val _ = emit "has_version_flag_def_typed" "has_version_flag_def";
val _ = emit "has_help_flag_def_typed" "has_help_flag_def";
val _ = emit "has_pancake_flag_def_typed" "has_pancake_flag_def";
val _ = emit "print_bool_def_typed" "print_bool_def";
val _ = emit "print_option_def_typed" "print_option_def";
val _ = emit "is_error_msg_def_typed" "is_error_msg_def";
val _ = emit "parse_bool_def_typed" "parse_bool_def";
val _ = emit "safe_substring_def_typed" "safe_substring_def";
val _ = emit "get_err_str_def_typed" "get_err_str_def";
val _ = emit "find_str_def_typed" "find_str_def";
val _ = emit "find_strs_def_typed" "find_strs_def";
val _ = emit "comma_tokens_def_typed" "comma_tokens_def";
val _ = emit "find_bool_def_typed" "find_bool_def";
val _ = emit "find_next_newline_def_typed" "find_next_newline_def";
val _ = emit "get_nth_line_def_typed" "get_nth_line_def";
