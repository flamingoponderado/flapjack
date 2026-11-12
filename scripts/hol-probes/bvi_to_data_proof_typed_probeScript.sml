(* Typed source declarations for bvi_to_dataProof (task 148). *)
load "preamble";
load "bvi_to_dataProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvi_to_dataProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="bvi_to_dataProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by bvi_to_dataProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of bvi_to_dataProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "var_corr_inter_typed" "var_corr_inter";
val _ = emit "get_vars_mk_wf_typed" "get_vars_mk_wf";
val _ = emit "get_vars_inter_typed" "get_vars_inter";
val _ = emit "data_to_bvi_result_def_typed" "data_to_bvi_result_def";
val _ = emit "data_to_bvi_result_eq_typed" "data_to_bvi_result_eq";
val _ = emit "var_corr_map_typed" "var_corr_map";
val _ = emit "get_vars_lift_thm_typed" "get_vars_lift_thm";
val _ = emit "data_to_bvi_v_list_to_v_APPEND_typed" "data_to_bvi_v_list_to_v_APPEND";
val _ = emit "data_to_bvi_v_list_to_v_Nil_typed" "data_to_bvi_v_list_to_v_Nil";
val _ = emit "v_to_bytes_eq_typed" "v_to_bytes_eq";
val _ = emit "v_to_words_eq_typed" "v_to_words_eq";
val _ = emit "code_rel_def_typed" "code_rel_def";
val _ = emit "data_to_bvi_ref_def_typed" "data_to_bvi_ref_def";
val _ = emit "data_to_bvi_v_def_typed" "data_to_bvi_v_def";
val _ = emit "data_to_bvi_v_Boolv_typed" "data_to_bvi_v_Boolv";
val _ = emit "data_to_bvi_v_Unit_typed" "data_to_bvi_v_Unit";
