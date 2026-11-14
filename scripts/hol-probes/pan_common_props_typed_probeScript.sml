(* Typed source declarations for pan_commonProps (task 148). *)
load "preamble";
load "pan_commonPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble pan_commonPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="pan_commonProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by pan_commonProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of pan_commonProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "MAP3_MAP2_typed" "MAP3_MAP2";
val _ = emit "MAX_LIST_add_not_mem_typed" "MAX_LIST_add_not_mem";
val _ = emit "MAX_LIST_i_genlist_typed" "MAX_LIST_i_genlist";
val _ = emit "all_distinct_drop_typed" "all_distinct_drop";
val _ = emit "all_distinct_el_fst_same_eq_typed" "all_distinct_el_fst_same_eq";
val _ = emit "all_distinct_take_typed" "all_distinct_take";
val _ = emit "all_distinct_take_frop_disjoint_typed" "all_distinct_take_frop_disjoint";
val _ = emit "disjoint_drop_take_sum_typed" "disjoint_drop_take_sum";
val _ = emit "disjoint_not_mem_el_typed" "disjoint_not_mem_el";
val _ = emit "disjoint_take_drop_sum_typed" "disjoint_take_drop_sum";
val _ = emit "distinct_lists_append_typed" "distinct_lists_append";
val _ = emit "distinct_lists_append_intro_typed" "distinct_lists_append_intro";
val _ = emit "distinct_lists_append_right_elim_typed" "distinct_lists_append_right_elim";
val _ = emit "distinct_lists_commutes_typed" "distinct_lists_commutes";
val _ = emit "distinct_lists_cons_typed" "distinct_lists_cons";
val _ = emit "distinct_lists_eq_disjoint_typed" "distinct_lists_eq_disjoint";
val _ = emit "distinct_lists_simp_cons_typed" "distinct_lists_simp_cons";
val _ = emit "el_pair_map_fst_el_typed" "el_pair_map_fst_el";
val _ = emit "el_reduc_tl_typed" "el_reduc_tl";
val _ = emit "genlist_distinct_max_typed" "genlist_distinct_max";
val _ = emit "map_the_some_cancel_typed" "map_the_some_cancel";
val _ = emit "map_append_eq_drop_typed" "map_append_eq_drop";
val _ = emit "max_foldr_lt_typed" "max_foldr_lt";
val _ = emit "mem_genlist_add_suc_val_typed" "mem_genlist_add_suc_val";
val _ = emit "opt_mmap_eq_some_typed" "opt_mmap_eq_some";
val _ = emit "opt_mmap_el_typed" "opt_mmap_el";
val _ = emit "opt_mmap_length_eq_typed" "opt_mmap_length_eq";
val _ = emit "opt_mmap_mem_defined_typed" "opt_mmap_mem_defined";
val _ = emit "opt_mmap_mem_func_typed" "opt_mmap_mem_func";
val _ = emit "opt_mmap_opt_map_typed" "opt_mmap_opt_map";
val _ = emit "set_eq_membership_typed" "set_eq_membership";
val _ = emit "ctxt_max_def_typed" "ctxt_max_def";
val _ = emit "no_overlap_def_typed" "no_overlap_def";
val _ = emit "update_eq_zip_flookup_typed" "update_eq_zip_flookup";
