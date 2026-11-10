(* Typed source declarations for bvl_to_bvi. *)
load "preamble";
load "bvl_to_bviTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvl_to_bviTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "destLet_def_typed" bvl_to_bviTheory.destLet_def;
val _ = show "compile_int_def_typed" bvl_to_bviTheory.compile_int_def;
val _ = show "global_count_sing_def_typed" bvl_to_bviTheory.global_count_sing_def;
val _ = show "compile_op_def_typed" bvl_to_bviTheory.compile_op_def;
val _ = show "ListLength_location_def_typed" bvl_to_bviTheory.ListLength_location_def;
val _ = show "FromListByte_location_def_typed" bvl_to_bviTheory.FromListByte_location_def;
val _ = show "ToListByte_location_def_typed" bvl_to_bviTheory.ToListByte_location_def;
val _ = show "SumListLength_location_def_typed" bvl_to_bviTheory.SumListLength_location_def;
val _ = show "ConcatByte_location_def_typed" bvl_to_bviTheory.ConcatByte_location_def;
val _ = show "AllocGlobal_code_def_typed" bvl_to_bviTheory.AllocGlobal_code_def;
val _ = show "CopyGlobals_code_def_typed" bvl_to_bviTheory.CopyGlobals_code_def;
val _ = show "InitGlobals_max_def_typed" bvl_to_bviTheory.InitGlobals_max_def;
val _ = show "InitGlobals_code_def_typed" bvl_to_bviTheory.InitGlobals_code_def;
val _ = show "ListLength_code_def_typed" bvl_to_bviTheory.ListLength_code_def;
val _ = show "FromListByte_code_def_typed" bvl_to_bviTheory.FromListByte_code_def;
val _ = show "ToListByte_code_def_typed" bvl_to_bviTheory.ToListByte_code_def;
val _ = show "SumListLength_code_def_typed" bvl_to_bviTheory.SumListLength_code_def;
val _ = show "ConcatByte_code_def_typed" bvl_to_bviTheory.ConcatByte_code_def;
val _ = show "stubs_def_typed" bvl_to_bviTheory.stubs_def;
val _ = show "get_names_def_typed" bvl_to_bviTheory.get_names_def;
