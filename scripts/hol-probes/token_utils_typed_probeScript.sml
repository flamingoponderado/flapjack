(* Typed captures for the remaining tokenUtilsTheory predicates and
   destructors (task 273): the token classifiers used by the CakeML
   lexer/parser ports and the three destructor characterisations. *)
load "tokenUtilsTheory";
open HolKernel Parse boolLib bossLib tokenUtilsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "tokenUtils", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in tokenUtils>\n");

val _ = emit "isInt_def_typed" "isInt_def";
val _ = emit "isString_def_typed" "isString_def";
val _ = emit "isAlphaT_def_typed" "isAlphaT_def";
val _ = emit "isSymbolT_def_typed" "isSymbolT_def";
val _ = emit "isTyvarT_def_typed" "isTyvarT_def";
val _ = emit "isWhitespaceT_def_typed" "isWhitespaceT_def";
val _ = emit "isCharT_def_typed" "isCharT_def";
val _ = emit "isWordT_def_typed" "isWordT_def";
val _ = emit "isLongidT_def_typed" "isLongidT_def";
val _ = emit "destREPLIDT_def_typed" "destREPLIDT_def";
val _ = emit "isAlphaSym_def_typed" "isAlphaSym_def";
val _ = emit "destLongidT_EQ_SOME_typed" "destLongidT_EQ_SOME";
val _ = emit "destAlphaT_EQ_SOME_typed" "destAlphaT_EQ_SOME";
val _ = emit "destSymbolT_EQ_SOME_typed" "destSymbolT_EQ_SOME";
