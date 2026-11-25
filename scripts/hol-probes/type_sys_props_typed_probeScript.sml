(* Typed captures for the typeSysProps reviewed rows (task 273). *)
load "preamble";
load "typeSysPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble typeSysPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy="typeSysProps",Name=name} of
    NONE => raise Fail (label ^ " is not exported by typeSysProps")
  | SOME (th,_) => show label th;

val _ = show "tenv_val_ok_nsEmpty_typed" typeSysPropsTheory.tenv_val_ok_nsEmpty;
val _ = show "tenv_ctor_ok_nsEmpty_typed" typeSysPropsTheory.tenv_ctor_ok_nsEmpty;
val _ = show "tenv_abbrev_ok_nsEmpty_typed" typeSysPropsTheory.tenv_abbrev_ok_nsEmpty;
val _ = show "tenv_ok_empty_typed" typeSysPropsTheory.tenv_ok_empty;
val _ = show "unchanged_tenv_typed" typeSysPropsTheory.unchanged_tenv;
val _ = emit "deBruijn_subst_tenvE_def_typed" "deBruijn_subst_tenvE_def";
val _ = emit "db_merge_def_typed" "db_merge_def";
val _ = emit "bind_tvar_rewrites_typed" "bind_tvar_rewrites";
val _ = emit "bind_tvar0_typed" "bind_tvar0";
val _ = emit "tveLookup_subst_none_typed" "tveLookup_subst_none";
val _ = emit "tveLookup_db_merge_none_typed" "tveLookup_db_merge_none";
val _ = emit "tveLookup_inc_none_typed" "tveLookup_inc_none";
val _ = emit "bind_var_list_append_typed" "bind_var_list_append";
val _ = emit "num_tvs_bind_var_list_typed" "num_tvs_bind_var_list";
val _ = emit "tveLookup_bvl_typed" "tveLookup_bvl";
val _ = emit "num_tvs_db_merge_typed" "num_tvs_db_merge";
val _ = emit "num_tvs_deBruijn_subst_tenvE_typed" "num_tvs_deBruijn_subst_tenvE";
val _ = emit "tenv_val_exp_ok_db_merge_typed" "tenv_val_exp_ok_db_merge";
val _ = emit "deBruijn_inc0_typed" "deBruijn_inc0";
val _ = emit "deBruijn_inc_deBruijn_inc_typed" "deBruijn_inc_deBruijn_inc";
val _ = emit "nil_deBruijn_inc_typed" "nil_deBruijn_inc";
val _ = emit "nil_deBruijn_subst_typed" "nil_deBruijn_subst";
val _ = emit "type_pes_def_typed" "type_pes_def";
val _ = emit "type_es_list_rel_typed" "type_es_list_rel";
val _ = emit "add_tenvE_nsAppend_typed" "add_tenvE_nsAppend";
val _ = emit "type_ds_empty_typed" "type_ds_empty";
val _ = emit "extend_dec_tenv_assoc_typed" "extend_dec_tenv_assoc";
val _ = emit "type_ctor_long_typed" "type_ctor_long";
val _ = emit "deBruijn_subst_id_typed" "deBruijn_subst_id";
val _ = emit "type_ps_length_typed" "type_ps_length";
val _ = emit "tenv_abbrev_ok_merge_typed" "tenv_abbrev_ok_merge";
val _ = emit "tenv_ctor_ok_merge_typed" "tenv_ctor_ok_merge";
val _ = emit "nsLookup_add_tenvE1_typed" "nsLookup_add_tenvE1";
val _ = emit "nsLookup_add_tenvE2_typed" "nsLookup_add_tenvE2";
val _ = emit "nsLookup_add_tenvE3_typed" "nsLookup_add_tenvE3";
val _ = emit "db_merge_bvl_typed" "db_merge_bvl";
val _ = emit "tveLookup_add_inc_typed" "tveLookup_add_inc";
val _ = emit "tveLookup_db_merge_some_typed" "tveLookup_db_merge_some";
val _ = emit "ctMap_ok_lookup_typed" "ctMap_ok_lookup";
val _ = emit "tenv_ctor_ok_lookup_typed" "tenv_ctor_ok_lookup";
val _ = emit "tenv_val_ok_add_tenvE_typed" "tenv_val_ok_add_tenvE";
val _ = emit "add_tenvE_bvl_typed" "add_tenvE_bvl";
val _ = emit "check_freevars_subst_list_typed" "check_freevars_subst_list";
val _ = emit "deBruijn_subst_freevars_typed" "deBruijn_subst_freevars";
val _ = emit "type_ds_sing_typed" "type_ds_sing";
