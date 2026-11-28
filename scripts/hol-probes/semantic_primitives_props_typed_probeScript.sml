(* Typed source declarations for semanticPrimitivesProps (task 148). *)
load "preamble";
load "semanticPrimitivesPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble semanticPrimitivesPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="semanticPrimitivesProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by semanticPrimitivesProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of semanticPrimitivesProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "every_error_result_def_typed" "every_error_result_def";
val _ = emit "every_result_def_typed" "every_result_def";
val _ = emit "do_opapp_cases_typed" "do_opapp_cases";
val _ = emit "extend_dec_env_assoc_typed" "extend_dec_env_assoc";
val _ = emit "sv_rel_mono_typed" "sv_rel_mono";
val _ = emit "exc_rel_def_typed" "exc_rel_def";
val _ = emit "result_rel_def_typed" "result_rel_def";
val _ = emit "sv_rel_cases_typed" "sv_rel_cases";
val _ = emit "sv_rel_def_typed" "sv_rel_def";
val _ = emit "map_error_result_def_typed" "map_error_result_def";
val _ = emit "map_error_result_Rtype_error_typed" "map_error_result_Rtype_error";
val _ = emit "map_error_result_I_typed" "map_error_result_I";
val _ = emit "map_result_def_typed" "map_result_def";
val _ = emit "map_result_Rval_typed" "map_result_Rval";
val _ = emit "map_result_Rerr_typed" "map_result_Rerr";
val _ = emit "build_rec_env_merge_typed" "build_rec_env_merge";
val _ = emit "find_recfun_ALOOKUP_typed" "find_recfun_ALOOKUP";
val _ = emit "lit_same_type_refl_typed" "lit_same_type_refl";
val _ = emit "lit_same_type_sym_typed" "lit_same_type_sym";
val _ = emit "map_match_def_typed" "map_match_def";
val _ = emit "do_conversion_check_type_typed" "do_conversion_check_type";
val _ = emit "do_arith_check_type_typed" "do_arith_check_type";
val _ = emit "shift_lookup_def_typed" "shift_lookup_def";
val _ = emit "do_shift_def_typed" "do_shift_def";
val _ = emit "pmatch_append_typed" "pmatch_append";
val _ = emit "pmatch_extend_typed" "pmatch_extend";
val _ = emit "pmatch_nsAppend_typed" "pmatch_nsAppend";
val _ = emit "pmatch_nsAppend_No_match_typed" "pmatch_nsAppend_No_match";
val _ = emit "pmatch_nsAppend_Match_typed" "pmatch_nsAppend_Match";
val _ = emit "pmatch_acc_typed" "pmatch_acc";
val _ = emit "do_app_cases_typed" "do_app_cases";
val _ = emit "do_app_NONE_ffi_typed" "do_app_NONE_ffi";
val _ = emit "do_app_SOME_ffi_same_typed" "do_app_SOME_ffi_same";
val _ = emit "do_app_ffi_unchanged_typed" "do_app_ffi_unchanged";
val _ = emit "do_app_ffi_changed_typed" "do_app_ffi_changed";
val _ = emit "do_app_not_timeout_typed" "do_app_not_timeout";
val _ = emit "do_app_type_error_typed" "do_app_type_error";
val _ = emit "dest_Refv_def_typed" "dest_Refv_def";
val _ = emit "sv_rel_O_typed" "sv_rel_O";
val _ = emit "FV_def_typed" "FV_def";
val _ = emit "FV_pes_MAP_typed" "FV_pes_MAP";
val _ = emit "FV_defs_MAP_typed" "FV_defs_MAP";
val _ = emit "FV_dec_def_typed" "FV_dec_def";
