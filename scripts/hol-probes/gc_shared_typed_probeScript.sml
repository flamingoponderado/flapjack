(* Typed source declarations for gc_shared (task 148). *)
load "preamble";
load "gc_sharedTheory";
open HolKernel Parse boolLib bossLib;
open preamble gc_sharedTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="gc_shared",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by gc_shared")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of gc_shared")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "heap_restrict_def_typed" "heap_restrict_def";
val _ = emit "heap_drop_def_typed" "heap_drop_def";
val _ = emit "heap_take_def_typed" "heap_take_def";
val _ = emit "heap_split_heap_length_typed" "heap_split_heap_length";
val _ = emit "heap_segment_IMP_typed" "heap_segment_IMP";
val _ = dt_label "gc_state_typed" "gc_state";
val _ = emit "empty_state_def_typed" "empty_state_def";
val _ = emit "heap_segment_def_typed" "heap_segment_def";
val _ = emit "heap_lookup_PREFIX_typed" "heap_lookup_PREFIX";
val _ = emit "heap_lookup_EXTEND_typed" "heap_lookup_EXTEND";
val _ = emit "isSomeDataOrForward_lemma_typed" "isSomeDataOrForward_lemma";
val _ = emit "isSomeForwardPointer_def_typed" "isSomeForwardPointer_def";
val _ = emit "isSomeDataOrForward_def_typed" "isSomeDataOrForward_def";
val _ = emit "FILTER_LEMMA_typed" "FILTER_LEMMA";
val _ = emit "heaps_similar_REFL_typed" "heaps_similar_REFL";
val _ = emit "heap_map_EMPTY_typed" "heap_map_EMPTY";
val _ = emit "heap_similar_Data_IMP_DataOrForward_typed" "heap_similar_Data_IMP_DataOrForward";
val _ = emit "heaps_similar_def_typed" "heaps_similar_def";
val _ = emit "heaps_similar_IMP_heap_length_typed" "heaps_similar_IMP_heap_length";
val _ = emit "heap_similar_Data_IMP_typed" "heap_similar_Data_IMP";
val _ = emit "heaps_similar_lemma_typed" "heaps_similar_lemma";
val _ = emit "NOT_IN_heap_map_typed" "NOT_IN_heap_map";
val _ = emit "IN_heap_map_IMP_typed" "IN_heap_map_IMP";
val _ = emit "heap_lookup_FLOOKUP_typed" "heap_lookup_FLOOKUP";
val _ = emit "heap_map_def_typed" "heap_map_def";
val _ = emit "heap_addresses_APPEND_typed" "heap_addresses_APPEND";
val _ = emit "heap_addresses_LESS_heap_length_typed" "heap_addresses_LESS_heap_length";
val _ = emit "heap_addresses_LESS_typed" "heap_addresses_LESS";
val _ = emit "MEM_IMP_heap_lookup_typed" "MEM_IMP_heap_lookup";
val _ = emit "heap_addresses_def_typed" "heap_addresses_def";
val _ = emit "gc_related_def_typed" "gc_related_def";
val _ = emit "ADDR_MAP_def_typed" "ADDR_MAP_def";
val _ = emit "ADDR_APPLY_def_typed" "ADDR_APPLY_def";
val _ = emit "ADDR_MAP_EQ_typed" "ADDR_MAP_EQ";
val _ = emit "ADDR_MAP_LENGTH_typed" "ADDR_MAP_LENGTH";
val _ = emit "ADDR_MAP_APPEND_typed" "ADDR_MAP_APPEND";
val _ = emit "MEM_ADDR_MAP_typed" "MEM_ADDR_MAP";
val _ = emit "gc_edge_def_typed" "gc_edge_def";
val _ = emit "reachable_addresses_def_typed" "reachable_addresses_def";
val _ = emit "heap_length_heap_expand_typed" "heap_length_heap_expand";
val _ = emit "heap_length_heap_filter_eq_typed" "heap_length_heap_filter_eq";
val _ = emit "heap_filter_aux_heap_addresses_UNION_typed" "heap_filter_aux_heap_addresses_UNION";
val _ = emit "heap_length_heap_filter_typed" "heap_length_heap_filter";
val _ = emit "heap_filter_aux_APPEND_typed" "heap_filter_aux_APPEND";
val _ = emit "heap_filter_aux_def_typed" "heap_filter_aux_def";
val _ = emit "heap_filter_def_typed" "heap_filter_def";
val _ = emit "heap_filter_EMPTY_typed" "heap_filter_EMPTY";
val _ = emit "gc_forward_ptr_thm_typed" "gc_forward_ptr_thm";
val _ = emit "gc_forward_ptr_ok_typed" "gc_forward_ptr_ok";
val _ = emit "gc_forward_ptr_def_typed" "gc_forward_ptr_def";
val _ = dt_label "heap_address_typed" "heap_address";
val _ = dt_label "heap_element_typed" "heap_element";
val _ = emit "heap_lookup_LESS_typed" "heap_lookup_LESS";
val _ = emit "el_length_def_typed" "el_length_def";
val _ = emit "heap_length_def_typed" "heap_length_def";
val _ = emit "heap_length_APPEND_typed" "heap_length_APPEND";
val _ = emit "heap_lookup_MEM_typed" "heap_lookup_MEM";
val _ = emit "heap_lookup_SPLIT_typed" "heap_lookup_SPLIT";
val _ = emit "heap_expand_def_typed" "heap_expand_def";
val _ = emit "heap_lookup_def_typed" "heap_lookup_def";
val _ = emit "heap_split_def_typed" "heap_split_def";
val _ = emit "isDataElement_def_typed" "isDataElement_def";
val _ = emit "isSomeDataElement_def_typed" "isSomeDataElement_def";
val _ = emit "isForwardPointer_def_typed" "isForwardPointer_def";
val _ = emit "roots_ok_def_typed" "roots_ok_def";
val _ = emit "heap_ok_def_typed" "heap_ok_def";
