(* Typed source declarations for bvl_to_bviProof (task 148). *)
load "preamble";
load "bvl_to_bviProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvl_to_bviProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="bvl_to_bviProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by bvl_to_bviProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of bvl_to_bviProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "adjust_bv_def_typed" "adjust_bv_def";
val _ = emit "adjust_bv_Unit_typed" "adjust_bv_Unit";
val _ = emit "adjust_bv_Boolv_typed" "adjust_bv_Boolv";
val _ = emit "aux_code_installed_def_typed" "aux_code_installed_def";
val _ = emit "aux_code_installed_subspt_typed" "aux_code_installed_subspt";
val _ = emit "names_ok_def_typed" "names_ok_def";
val _ = emit "bv_ok_def_typed" "bv_ok_def";
val _ = emit "state_rel_def_typed" "state_rel_def";
val _ = emit "state_rel_FLOOKUP_byteArray_typed" "state_rel_FLOOKUP_byteArray";
val _ = emit "state_rel_FLOOKUP_valueArray_typed" "state_rel_FLOOKUP_valueArray";
val _ = emit "state_rel_FLOOKUP_MutBlock_typed" "state_rel_FLOOKUP_MutBlock";
val _ = emit "state_rel_FLOOKUP_Thunk_typed" "state_rel_FLOOKUP_Thunk";
val _ = emit "state_ok_def_typed" "state_ok_def";
val _ = emit "list_to_v_ok_typed" "list_to_v_ok";
val _ = emit "list_to_v_ok_APPEND_typed" "list_to_v_ok_APPEND";
val _ = emit "find_code_bv_ok_typed" "find_code_bv_ok";
val _ = emit "do_build_ok_typed" "do_build_ok";
val _ = emit "do_app_ok_typed" "do_app_ok";
val _ = emit "evaluate_ok_typed" "evaluate_ok";
val _ = emit "compile_inc_no_mutcons_typed" "compile_inc_no_mutcons";
val _ = emit "bvi_tailrec_compile_prog_no_mutcons_typed" "bvi_tailrec_compile_prog_no_mutcons";
