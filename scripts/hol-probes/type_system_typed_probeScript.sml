(* Typed source declarations for typeSystem (task 148). *)
load "preamble";
load "typeSystemTheory";
open HolKernel Parse boolLib bossLib;
open preamble typeSystemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="typeSystem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by typeSystem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of typeSystem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "Tarray_num_def_typed" "Tarray_num_def";
val _ = emit "Tbool_num_def_typed" "Tbool_num_def";
val _ = emit "Tchar_num_def_typed" "Tchar_num_def";
val _ = emit "Texn_num_def_typed" "Texn_num_def";
val _ = emit "Tfn_num_def_typed" "Tfn_num_def";
val _ = emit "Tint_num_def_typed" "Tint_num_def";
val _ = emit "Tlist_num_def_typed" "Tlist_num_def";
val _ = emit "Tref_num_def_typed" "Tref_num_def";
val _ = emit "Tstring_num_def_typed" "Tstring_num_def";
val _ = emit "Ttup_num_def_typed" "Ttup_num_def";
val _ = emit "Tvector_num_def_typed" "Tvector_num_def";
val _ = emit "Tword64_num_def_typed" "Tword64_num_def";
val _ = emit "Tword8_num_def_typed" "Tword8_num_def";
val _ = emit "Tword8array_num_def_typed" "Tword8array_num_def";
val _ = emit "Tdouble_num_def_typed" "Tdouble_num_def";
val _ = emit "Tarray_def_typed" "Tarray_def";
val _ = emit "Tbool_def_typed" "Tbool_def";
val _ = emit "Tchar_def_typed" "Tchar_def";
val _ = emit "Texn_def_typed" "Texn_def";
val _ = emit "Tfn_def_typed" "Tfn_def";
val _ = emit "Tint_def_typed" "Tint_def";
val _ = emit "Tlist_def_typed" "Tlist_def";
val _ = emit "Tref_def_typed" "Tref_def";
val _ = emit "Tstring_def_typed" "Tstring_def";
val _ = emit "Ttup_def_typed" "Ttup_def";
val _ = emit "Tvector_def_typed" "Tvector_def";
val _ = emit "Tword64_def_typed" "Tword64_def";
val _ = emit "Tword8_def_typed" "Tword8_def";
val _ = emit "Tword8array_def_typed" "Tword8array_def";
val _ = emit "Tdouble_def_typed" "Tdouble_def";
val _ = dt_label "t_typed" "t";
val _ = emit "check_freevars_def_typed" "check_freevars_def";
val _ = emit "check_freevars_ast_def_typed" "check_freevars_ast_def";
val _ = emit "deBruijn_inc_def_typed" "deBruijn_inc_def";
val _ = emit "deBruijn_subst_def_typed" "deBruijn_subst_def";
val _ = dt_label "tenv_val_exp_typed" "tenv_val_exp";
val _ = emit "bind_tvar_def_typed" "bind_tvar_def";
val _ = emit "opt_bind_name_def_typed" "opt_bind_name_def";
val _ = emit "tveLookup_def_typed" "tveLookup_def";
val _ = dt_label "type_env_typed" "type_env";
val _ = emit "extend_dec_tenv_def_typed" "extend_dec_tenv_def";
val _ = emit "lookup_varE_def_typed" "lookup_varE_def";
val _ = emit "lookup_var_def_typed" "lookup_var_def";
val _ = emit "num_tvs_def_typed" "num_tvs_def";
val _ = emit "bind_var_list_def_typed" "bind_var_list_def";
val _ = emit "type_subst_def_typed" "type_subst_def";
val _ = emit "check_type_names_def_typed" "check_type_names_def";
val _ = emit "type_name_subst_def_typed" "type_name_subst_def";
val _ = emit "t_of_def_typed" "t_of_def";
val _ = emit "supported_test_def_typed" "supported_test_def";
val _ = emit "supported_arith_def_typed" "supported_arith_def";
val _ = emit "supported_conversion_def_typed" "supported_conversion_def";
val _ = emit "type_op_def_typed" "type_op_def";
val _ = emit "is_value_def_typed" "is_value_def";
val _ = emit "check_ctor_tenv_def_typed" "check_ctor_tenv_def";
val _ = emit "build_ctor_tenv_def_typed" "build_ctor_tenv_def";
val _ = emit "tenv_add_tvs_def_typed" "tenv_add_tvs_def";
val _ = emit "tscheme_inst_def_typed" "tscheme_inst_def";
val _ = emit "tenvLift_def_typed" "tenvLift_def";
val _ = emit "prim_type_nums_def_typed" "prim_type_nums_def";
