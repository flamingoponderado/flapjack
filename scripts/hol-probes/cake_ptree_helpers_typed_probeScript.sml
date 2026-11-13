(* Typed captures for the tokenUtils token destructors and the
   cmlPtreeConversion helper definitions used by the exact CakeParser
   parsetree ports (task 160). *)
load "preamble";
load "tokenUtilsTheory";
load "cmlPtreeConversionTheory";
open HolKernel Parse boolLib bossLib;
open preamble tokenUtilsTheory cmlPtreeConversionTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "destTOK_def_typed" tokenUtilsTheory.destTOK_def;
val _ = show "destLongidT_def_typed" tokenUtilsTheory.destLongidT_def;
val _ = show "destTyvarPT_def_typed" tokenUtilsTheory.destTyvarPT_def;
val _ = show "destAlphaT_def_typed" tokenUtilsTheory.destAlphaT_def;
val _ = show "destSymbolT_def_typed" tokenUtilsTheory.destSymbolT_def;
val _ = show "destIntT_def_typed" tokenUtilsTheory.destIntT_def;
val _ = show "destCharT_def_typed" tokenUtilsTheory.destCharT_def;
val _ = show "destStringT_def_typed" tokenUtilsTheory.destStringT_def;
val _ = show "destWordT_def_typed" tokenUtilsTheory.destWordT_def;
val _ = show "destFFIT_def_typed" tokenUtilsTheory.destFFIT_def;
val _ = show "isLower_def_typed" stringTheory.isLower_def;
val _ = show "isUpper_def_typed" stringTheory.isUpper_def;
val _ = show "isAlpha_def_typed" stringTheory.isAlpha_def;
val _ = show "oHD_def_typed" listTheory.oHD_def;
val _ = show "ifM_def_typed" cmlPtreeConversionTheory.ifM_def;
val _ = show "tokcheckl_def_typed" cmlPtreeConversionTheory.tokcheckl_def;
val _ = show "singleSymP_def_typed" cmlPtreeConversionTheory.singleSymP_def;
val _ = show "isSymbolicConstructor_def_typed"
  cmlPtreeConversionTheory.isSymbolicConstructor_def;
val _ = show "isConstructor_def_typed" cmlPtreeConversionTheory.isConstructor_def;
