(* Typed source declarations for bvl_to_bvi (task 148). *)
load "preamble";
load "bvl_to_bviTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvl_to_bviTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="bvl_to_bvi",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by bvl_to_bvi")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of bvl_to_bvi")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "AllocGlobal_location_def_typed" "AllocGlobal_location_def";
val _ = emit "CopyGlobals_location_def_typed" "CopyGlobals_location_def";
val _ = emit "InitGlobals_location_def_typed" "InitGlobals_location_def";
val _ = dt_label "config_typed" "config";
val _ = emit "default_config_def_typed" "default_config_def";
val _ = emit "destLet_def_typed" "destLet_def";
val _ = emit "compile_int_def_typed" "compile_int_def";
val _ = emit "global_count_sing_def_typed" "global_count_sing_def";
val _ = emit "compile_op_def_typed" "compile_op_def";
val _ = emit "ListLength_location_def_typed" "ListLength_location_def";
val _ = emit "FromListByte_location_def_typed" "FromListByte_location_def";
val _ = emit "ToListByte_location_def_typed" "ToListByte_location_def";
val _ = emit "SumListLength_location_def_typed" "SumListLength_location_def";
val _ = emit "ConcatByte_location_def_typed" "ConcatByte_location_def";
val _ = emit "AllocGlobal_code_def_typed" "AllocGlobal_code_def";
val _ = emit "CopyGlobals_code_def_typed" "CopyGlobals_code_def";
val _ = emit "InitGlobals_max_def_typed" "InitGlobals_max_def";
val _ = emit "InitGlobals_code_def_typed" "InitGlobals_code_def";
val _ = emit "ListLength_code_def_typed" "ListLength_code_def";
val _ = emit "FromListByte_code_def_typed" "FromListByte_code_def";
val _ = emit "ToListByte_code_def_typed" "ToListByte_code_def";
val _ = emit "SumListLength_code_def_typed" "SumListLength_code_def";
val _ = emit "ConcatByte_code_def_typed" "ConcatByte_code_def";
val _ = emit "stubs_def_typed" "stubs_def";
val _ = emit "get_names_def_typed" "get_names_def";
val _ = emit "compile_aux_def_typed" "compile_aux_def";
val _ = emit "compile_exps_sing_def_typed" "compile_exps_sing_def";
val _ = emit "compile_single_def_typed" "compile_single_def";
val _ = emit "compile_list_def_typed" "compile_list_def";
val _ = emit "compile_inc_def_typed" "compile_inc_def";
