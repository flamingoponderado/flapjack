(* Typed source declarations for gen_gc_partial (task 148). *)
load "preamble";
load "gen_gc_partialTheory";
open HolKernel Parse boolLib bossLib;
open preamble gen_gc_partialTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="gen_gc_partial",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by gen_gc_partial")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of gen_gc_partial")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "partial_gc_related_typed" "partial_gc_related";
val _ = emit "isSomeDataElement_heap_lookup_heap_expand_typed" "isSomeDataElement_heap_lookup_heap_expand";
val _ = emit "new_f_def_typed" "new_f_def";
val _ = emit "f_old_ptrs_def_typed" "f_old_ptrs_def";
val _ = emit "f_old_ptrs_finite_typed" "f_old_ptrs_finite";
val _ = emit "isSomeDataElement_to_gen_heap_list_typed" "isSomeDataElement_to_gen_heap_list";
val _ = emit "gc_move_ref_list_heap_length_typed" "gc_move_ref_list_heap_length";
val _ = dt_label "data_sort_typed" "data_sort";
val _ = emit "to_gen_heap_address_def_typed" "to_gen_heap_address_def";
val _ = emit "to_gen_conf_def_typed" "to_gen_conf_def";
val _ = emit "to_gen_heap_element_def_typed" "to_gen_heap_element_def";
val _ = emit "to_gen_heap_list_def_typed" "to_gen_heap_list_def";
val _ = emit "to_gen_heap_def_typed" "to_gen_heap_def";
val _ = emit "to_gen_state_def_typed" "to_gen_state_def";
val _ = emit "to_gen_roots_def_typed" "to_gen_roots_def";
val _ = emit "refs_to_roots_def_typed" "refs_to_roots_def";
val _ = emit "heap_element_is_ref_def_typed" "heap_element_is_ref_def";
val _ = emit "heap_gen_ok_def_typed" "heap_gen_ok_def";
val _ = emit "gen_inv_def_typed" "gen_inv_def";
val _ = emit "has_old_ptr_def_typed" "has_old_ptr_def";
val _ = emit "all_old_ptrs_def_typed" "all_old_ptrs_def";
val _ = emit "sim_inv_def_typed" "sim_inv_def";
val _ = emit "heap_length_to_gen_heap_list_typed" "heap_length_to_gen_heap_list";
val _ = emit "similar_ptr_def_typed" "similar_ptr_def";
val _ = emit "similar_data_def_typed" "similar_data_def";
val _ = emit "LIST_REL_similar_data_IMP_typed" "LIST_REL_similar_data_IMP";
val _ = emit "gc_move_list_heap_length_typed" "gc_move_list_heap_length";
val _ = emit "gc_forward_ptr_heap_length_typed" "gc_forward_ptr_heap_length";
val _ = emit "gc_move_heap_length_typed" "gc_move_heap_length";
val _ = dt_label "gen_gc_partial_conf_typed" "gen_gc_partial_conf";
val _ = emit "gc_move_def_typed" "gc_move_def";
val _ = emit "gc_move_list_def_typed" "gc_move_list_def";
val _ = emit "gc_move_ref_list_def_typed" "gc_move_ref_list_def";
val _ = emit "gc_move_data_def_typed" "gc_move_data_def";
val _ = emit "partial_gc_def_typed" "partial_gc_def";
