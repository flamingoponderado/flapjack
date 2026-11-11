(* Typed source declarations for cmlPtreeConversion. *)
load "preamble";
load "cmlPtreeConversionTheory";
open HolKernel Parse boolLib bossLib;
open preamble cmlPtreeConversionTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "tokcheck_def_typed" cmlPtreeConversionTheory.tokcheck_def;
val _ = show "Long_Short_def_typed" cmlPtreeConversionTheory.Long_Short_def;
val _ = show "ptree_UQTyop_def_typed" cmlPtreeConversionTheory.ptree_UQTyop_def;
val _ = show "ptree_TyvarN_def_typed" cmlPtreeConversionTheory.ptree_TyvarN_def;
val _ = show "ptree_Tyop_def_typed" cmlPtreeConversionTheory.ptree_Tyop_def;
val _ = show "ptree_V_def_typed" cmlPtreeConversionTheory.ptree_V_def;
val _ = show "ptree_FQV_def_typed" cmlPtreeConversionTheory.ptree_FQV_def;
val _ = show "tuplify_def_typed" cmlPtreeConversionTheory.tuplify_def;
val _ = show "ptree_UQConstructorName_def_typed" cmlPtreeConversionTheory.ptree_UQConstructorName_def;
val _ = show "ptree_ConstructorName_def_typed" cmlPtreeConversionTheory.ptree_ConstructorName_def;
val _ = show "ptree_OpID_def_typed" cmlPtreeConversionTheory.ptree_OpID_def;
val _ = show "EtoPat_def_typed" cmlPtreeConversionTheory.EtoPat_def;
val _ = show "Papply_def_typed" cmlPtreeConversionTheory.Papply_def;
val _ = show "maybe_handleRef_def_typed" cmlPtreeConversionTheory.maybe_handleRef_def;
val _ = show "ptree_Eliteral_def_typed" cmlPtreeConversionTheory.ptree_Eliteral_def;
val _ = show "ptree_Op_def_typed" cmlPtreeConversionTheory.ptree_Op_def;
val _ = show "mk_binop_def_typed" cmlPtreeConversionTheory.mk_binop_def;
val _ = show "bind_loc_def_typed" cmlPtreeConversionTheory.bind_loc_def;
val _ = show "strip_loc_expr_def_typed" cmlPtreeConversionTheory.strip_loc_expr_def;
val _ = show "mkAst_App_def_typed" cmlPtreeConversionTheory.mkAst_App_def;
val _ = show "dePat_def_typed" cmlPtreeConversionTheory.dePat_def;
val _ = show "mkFun_def_typed" cmlPtreeConversionTheory.mkFun_def;
val _ = show "letFromPat_def_typed" cmlPtreeConversionTheory.letFromPat_def;
val _ = show "ptree_StructName_def_typed" cmlPtreeConversionTheory.ptree_StructName_def;
