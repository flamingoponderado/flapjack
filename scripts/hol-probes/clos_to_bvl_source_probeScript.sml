(* Typed source declarations for clos_to_bvl. *)
load "preamble";
load "clos_to_bvlTheory";
open HolKernel Parse boolLib bossLib;
open preamble clos_to_bvlTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "part_hash_def_typed" clos_to_bvlTheory.part_hash_def;
val _ = show "add_part_def_typed" clos_to_bvlTheory.add_part_def;
val _ = show "add_parts_def_typed" clos_to_bvlTheory.add_parts_def;
val _ = show "compile_const_def_typed" clos_to_bvlTheory.compile_const_def;
val _ = show "num_added_globals_def_typed" clos_to_bvlTheory.num_added_globals_def;
val _ = show "partial_app_label_table_loc_def_typed" clos_to_bvlTheory.partial_app_label_table_loc_def;
val _ = show "compile_op_def_typed" clos_to_bvlTheory.compile_op_def;
val _ = show "mk_const_def_typed" clos_to_bvlTheory.mk_const_def;
val _ = show "mk_label_def_typed" clos_to_bvlTheory.mk_label_def;
val _ = show "mk_el_def_typed" clos_to_bvlTheory.mk_el_def;
val _ = show "num_stubs_def_typed" clos_to_bvlTheory.num_stubs_def;
val _ = show "generic_app_fn_location_def_typed" clos_to_bvlTheory.generic_app_fn_location_def;
val _ = show "partial_app_fn_location_def_typed" clos_to_bvlTheory.partial_app_fn_location_def;
val _ = show "partial_app_fn_location_code_def_typed" clos_to_bvlTheory.partial_app_fn_location_code_def;
val _ = show "code_merge_def_typed" clos_to_bvlTheory.code_merge_def;
val _ = show "code_sort_def_typed" clos_to_bvlTheory.code_sort_def;
val _ = show "free_let_def_typed" clos_to_bvlTheory.free_let_def;
val _ = show "code_for_recc_case_def_typed" clos_to_bvlTheory.code_for_recc_case_def;
val _ = show "build_aux_def_typed" clos_to_bvlTheory.build_aux_def;
val _ = show "add_src_names_def_typed" clos_to_bvlTheory.add_src_names_def;
val _ = show "get_src_names_sing_def_typed" clos_to_bvlTheory.get_src_names_sing_def;
val _ = show "get_src_names_def_typed" clos_to_bvlTheory.get_src_names_def;
val _ = show "mk_cl_call_def_typed" clos_to_bvlTheory.mk_cl_call_def;
val _ = show "generate_partial_app_closure_fn_def_typed" clos_to_bvlTheory.generate_partial_app_closure_fn_def;
val _ = show "extract_name_def_typed" clos_to_bvlTheory.extract_name_def;
val _ = show "make_name_alist_def_typed" clos_to_bvlTheory.make_name_alist_def;
val _ = show "recc_Let_def_typed" clos_to_bvlTheory.recc_Let_def;
val _ = show "recc_Let0_def_typed" clos_to_bvlTheory.recc_Let0_def;
val _ = show "recc_Lets_def_typed" clos_to_bvlTheory.recc_Lets_def;
val _ = show "build_recc_lets_def_typed" clos_to_bvlTheory.build_recc_lets_def;
val _ = show "generate_generic_app_def_typed" clos_to_bvlTheory.generate_generic_app_def;
val _ = show "check_closure_def_typed" clos_to_bvlTheory.check_closure_def;
val _ = show "init_code_def_typed" clos_to_bvlTheory.init_code_def;
val _ = show "init_globals_def_typed" clos_to_bvlTheory.init_globals_def;
val _ = show "force_thunk_code_def_typed" clos_to_bvlTheory.force_thunk_code_def;
val _ = show "build_aux_acc_typed" clos_to_bvlTheory.build_aux_acc;
val _ = show "build_aux_LENGTH_typed" clos_to_bvlTheory.build_aux_LENGTH;
val _ = show "build_aux_MEM_typed" clos_to_bvlTheory.build_aux_MEM;
val _ = show "build_aux_MOVE_typed" clos_to_bvlTheory.build_aux_MOVE;
val _ = show "compile_exps_acc_typed" clos_to_bvlTheory.compile_exps_acc;
val _ = show "compile_exps_LENGTH_typed" clos_to_bvlTheory.compile_exps_LENGTH;
val _ = show "compile_inc_def_typed" clos_to_bvlTheory.compile_inc_def;
