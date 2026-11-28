(* Typed source declarations for the result relations in
   semantics/proofs/semanticPrimitivesPropsScript.sml (task 273). *)
load "preamble";
load "semanticPrimitivesPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble semanticPrimitivesPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy = "semanticPrimitivesProps", Name = name};

fun show label th =
  (print (label ^ "=");
   app (fn h => (print_term h; print " ==> ")) (hyp th);
   print_term (concl th);
   print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by semanticPrimitivesProps")
  | SOME (th, _) => show label th;

val _ = emit "exc_rel_raise1_typed" "exc_rel_raise1";
val _ = emit "exc_rel_raise2_typed" "exc_rel_raise2";
val _ = emit "exc_rel_type_error1_typed" "exc_rel_type_error1";
val _ = emit "exc_rel_type_error2_typed" "exc_rel_type_error2";
val _ = emit "exc_rel_refl_typed" "exc_rel_refl";
val _ = emit "exc_rel_trans_typed" "exc_rel_trans";
val _ = emit "result_rel_Rval_typed" "result_rel_Rval";
val _ = emit "result_rel_Rerr1_typed" "result_rel_Rerr1";
val _ = emit "result_rel_Rerr2_typed" "result_rel_Rerr2";
val _ = emit "result_rel_refl_typed" "result_rel_refl";
val _ = emit "result_rel_trans_typed" "result_rel_trans";

(* Store-entry operations and the opening record/Bool laws. *)
val _ = emit "map_sv_def_typed" "map_sv_def";
val _ = emit "is_Refv_def_typed" "is_Refv_def";
val _ = emit "sv_every_def_typed" "sv_every_def";
val _ = emit "store_v_vs_def_typed" "store_v_vs_def";
val _ = emit "store_vs_def_typed" "store_vs_def";
val _ = emit "map_sv_compose_typed" "map_sv_compose";
val _ = emit "sv_rel_refl_typed" "sv_rel_refl";
val _ = emit "sv_rel_trans_typed" "sv_rel_trans";
val _ = emit "with_same_v_typed" "with_same_v";
val _ = emit "unchanged_env_typed" "unchanged_env";
val _ = emit "with_same_clock_typed" "with_same_clock";
val _ = emit "Boolv_11_typed" "Boolv_11";

(* Declaration constructors, primitive-type cases and lookup. *)
val _ = emit "ctors_of_tdef_def_typed" "ctors_of_tdef_def";
val _ = emit "ctors_of_dec_def_typed" "ctors_of_dec_def";
val _ = emit "prim_type_cases_typed" "prim_type_cases";
val _ = emit "nat_to_v_11_typed" "nat_to_v_11";
val _ = emit "find_recfun_el_typed" "find_recfun_el";

(* Store-value list theorems and concrete-value characterizations. *)
val _ = emit "EVERY_sv_every_MAP_map_sv_typed" "EVERY_sv_every_MAP_map_sv";
val _ = emit "EVERY_sv_every_EVERY_store_vs_typed" "EVERY_sv_every_EVERY_store_vs";
val _ = emit "EVERY_store_vs_intro_typed" "EVERY_store_vs_intro";
val _ = emit "LIST_REL_store_vs_intro_typed" "LIST_REL_store_vs_intro";
val _ = emit "concrete_v_list_typed" "concrete_v_list";
val _ = emit "concrete_v_simps_typed" "concrete_v_simps";
val _ = emit "do_con_check_build_conv_typed" "do_con_check_build_conv";
