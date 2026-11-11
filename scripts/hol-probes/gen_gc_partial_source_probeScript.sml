(* Typed source declarations for gen_gc_partial. *)
load "preamble";
load "gen_gc_partialTheory";
open HolKernel Parse boolLib bossLib;
open preamble gen_gc_partialTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun replay label term = (print (label ^ "="); print_term term; print "\n");

val _ = replay "gc_move_refs_isForwardPointer_typed" ``∀refs refs1 state1 state.
    (gc_move_ref_list conf state refs = (refs1,state1)) ∧
    (FILTER isForwardPointer refs = []) ⇒
    (FILTER isForwardPointer refs1 = [])``;
val _ = show "isSomeDataElement_heap_lookup_heap_expand_typed" gen_gc_partialTheory.isSomeDataElement_heap_lookup_heap_expand;
val _ = replay "partial_gc_heap_length_lemma_typed" ``!roots'.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    (gen_gc (to_gen_conf conf) (gen_roots,gen_heap) =
      (roots',to_gen_state conf state1)) /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs)) /\
    (conf.gen_start ≤ conf.refs_start) /\
    (conf.refs_start ≤ conf.limit) /\
    roots_ok gen_roots gen_heap /\
    heap_ok gen_heap (to_gen_conf conf).limit
    ==>
    (heap_length (state1.old ++ state1.h1 ++ heap_expand state1.n) = conf.refs_start)``;
val _ = replay "heap_lookup_old_IMP_typed" ``!i ys.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    (heap_lookup i heap = SOME (DataElement xs l d)) /\
    (i < conf.gen_start) ==>
    (heap_lookup i (state1.old ++ ys) = SOME (DataElement xs l d))``;
val _ = replay "heap_lookup_refs_IMP_typed" ``!x.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    (heap_lookup x heap = SOME (DataElement xs l d)) /\
    (heap_length (state1.old ++ state1.h1 ++ heap_expand state1.n) = conf.refs_start) /\
    (conf.refs_start ≤ x)
    ==>
    ?xs1.
    (heap_lookup x (state1.old ++ state1.h1 ++ heap_expand state1.n ++ state1.r1) =
      SOME (DataElement xs1 l d))``;
val _ = replay "gc_move_list_similar_typed" ``!xs state1 ys state2.
      (gc_move_list conf state1 xs = (ys,state2)) ==>
      LIST_REL (similar_ptr conf) xs ys``;
val _ = replay "gc_move_ref_list_similar_typed" ``!heap_refs state refs' state' conf.
      (gc_move_ref_list conf state heap_refs = (refs',state')) ==>
      LIST_REL (similar_data conf) heap_refs refs'``;
val _ = replay "heap_ok_simulation_typed" ``!heap heap_old heap_current heap_refs (conf :'b gen_gc_partial_conf).
    heap_ok (heap :('a,'b) heap_element list) conf.limit /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs)) /\
    (conf.gen_start ≤ conf.refs_start) /\
    (conf.refs_start ≤ conf.limit)
    ==>
    heap_ok
      (MAP (to_gen_heap_element conf) heap_current)
      (to_gen_conf conf).limit``;
val _ = replay "MEM_to_gen_roots_IMP_MEM_typed" ``!roots.
    MEM (Pointer ptr u) (to_gen_roots conf roots)
    ==>
    ?ptr' u'.
    MEM (Pointer ptr' u') roots /\
    (ptr = ptr' - conf.gen_start) /\
    (u = Real u') /\
    (conf.gen_start <= ptr') /\
    (ptr' < conf.refs_start)``;
val _ = replay "MEM_refs_to_roots_IMP_MEM_typed" ``!heap_refs.
    MEM (Pointer ptr u) (refs_to_roots conf heap_refs) ==>
    ?xs l d ptr' u'.
    MEM (DataElement xs l d) heap_refs /\
    MEM (Pointer ptr' u') xs /\
    (ptr = ptr' - conf.gen_start) /\
    (u = Real u') /\
    (conf.gen_start <= ptr') /\
    (ptr' < conf.refs_start)``;
val _ = show "isSomeDataElement_to_gen_heap_list_typed" gen_gc_partialTheory.isSomeDataElement_to_gen_heap_list;
val _ = replay "roots_ok_simulation_typed" ``!roots heap heap_old heap_current heap_refs (conf :'b gen_gc_partial_conf).
    roots_ok roots (heap :('a,'b) heap_element list) /\
    heap_ok heap conf.limit /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs)) /\
    (conf.gen_start ≤ conf.refs_start)
    ==>
    roots_ok
      (to_gen_roots conf roots ++ refs_to_roots conf heap_refs)
      (MAP (to_gen_heap_element conf) heap_current)``;
val _ = replay "partial_gc_simulation_typed" ``!conf roots heap0 roots1 state1 heap0_old heap0_current heap0_refs
     new_roots new_state.
      (partial_gc conf (roots,heap0) = (roots1,state1)) /\
      heap_gen_ok heap0 conf /\
      conf.gen_start ≤ conf.refs_start ∧ conf.refs_start ≤ conf.limit /\
      (heap_segment (conf.gen_start,conf.refs_start) heap0
        = SOME (heap0_old,heap0_current,heap0_refs)) /\
      EVERY (\e. ~(heap_element_is_ref conf e)) (heap0_old ++ heap0_current) /\
      EVERY isDataElement heap0_refs /\
      roots_ok roots heap0 /\
      (gen_gc (to_gen_conf conf)
        (to_gen_roots conf roots ++ refs_to_roots conf heap0_refs,
         to_gen_heap_list conf heap0_current) = (new_roots,new_state)) /\
      heap_ok heap0 conf.limit /\ new_state.ok ==>
      (new_roots = to_gen_roots conf roots1 ++ refs_to_roots conf state1.r1) /\
      (new_state = to_gen_state conf state1) /\
      sim_inv conf heap0 state1 /\ (state1.h2 = []) /\ state1.ok``;
val _ = replay "gc_move_data_r1_1137_typed" ``(gc_move_data conf state).r1 = state.r1``;
val _ = replay "gc_move_ref_list_heap_length_1123_typed" ``!h x state state'. (gc_move_ref_list conf state h = (x,state')) ==> (heap_length state.heap = heap_length state'.heap)``;
val _ = replay "gc_move_data_h2_typed" ``!conf state.
      (gc_move_data conf state).ok ==>
      ((gc_move_data conf state).h2 = [])``;
val _ = replay "gc_move_with_refs_prime_typed" ``!l. (gc_move conf (state with <|r2 := []; r1 := refs |>) l =
         let (xs,s) = gc_move conf state l in (xs,s with <|r2 := []; r1 := refs |>))``;
val _ = replay "gc_move_list_with_refs_prime_typed" ``!l state.
      (gc_move_list conf (state with <|r2 := [] ; r1 := refs |>) l =
       let (xs,s) = gc_move_list conf state l in (xs,s with <|r2 := []; r1 := refs|>))``;
val _ = replay "gc_move_data_with_refs_prime_typed" ``!conf state refs.
     (gc_move_data conf (state with <|r2 := []; r1 := refs|>) =
     (gc_move_data conf state) with <|r2 := []; r1 := refs|>)``;
val _ = replay "gc_move_data_simulation_typed" ``!conf state heap0 state' ptr1' state1'.
      (gc_move_data conf state = state') /\
      sim_inv conf heap0 state /\
      (∀ptrs l d ptr' u. MEM (Pointer ptr' u) ptrs /\ MEM (DataElement ptrs l d) (state.h2++state.heap) ⇒ ptr' < heap_length state.heap) /\
      (heap_length state.heap = conf.limit) /\
      (gen_gc$gc_move_data
         (to_gen_conf conf)
         (to_gen_state conf state) = state1') /\ state1'.ok ==>
      sim_inv conf heap0 state' /\
      (state1' = to_gen_state conf state')``;
val _ = replay "gc_move_data_pres_typed" ``(gc_move conf state x = (x1,state1))
   ==> (MEM (DataElement xs l dd) (state1.heap++state1.h2)
        = MEM (DataElement xs l dd) (state.heap++state.h2))``;
val _ = replay "gc_move_list_data_pres_typed" ``!x conf state x1 state1 xs l dd.
   (gc_move_list conf state x = (x1,state1))
   ==> (MEM (DataElement xs l dd) (state1.heap++state1.h2)
        = MEM (DataElement xs l dd) (state.heap++state.h2))``;
val _ = replay "gc_move_ref_list_data_pres_typed" ``!x conf state x1 state1 xs l dd.
   (gc_move_ref_list conf state x = (x1,state1))
   ==> (MEM (DataElement xs l dd) (state1.heap++state1.h2)
        = MEM (DataElement xs l dd) (state.heap++state.h2))``;
val _ = replay "gc_move_ref_list_simulation_typed" ``!conf state refs0 heap0 state1 state1' refs1 refs1'.
    (gc_move_ref_list conf (state : ('b,'a) gc_state) (refs0 : ('b,'a) heap_element list)
      = (refs1,state1)) /\
    (gc_move_list (to_gen_conf conf)
                  (to_gen_state conf state)
                  (refs_to_roots conf refs0)
      = (refs1',state1')) /\ state1'.ok /\
    sim_inv conf heap0 state /\
    (∀ptrs l d ptr' u. MEM (Pointer ptr' u) ptrs /\ MEM (DataElement ptrs l d) refs0 ⇒ ptr' < heap_length state.heap) ∧
    (heap_length state.heap = conf.limit) /\
    EVERY isDataElement refs0
    ==>
    sim_inv conf heap0 state1 /\
    (refs1' = refs_to_roots conf refs1) /\
    (state1' = to_gen_state conf state1) /\
    has_old_ptr conf refs1 SUBSET has_old_ptr conf refs0``;
val _ = replay "gc_move_list_simulation_typed" ``!ptr ptr' state state' ptr1' state1'.
      (gc_move_list conf state ptr = (ptr', state')) /\
      sim_inv conf heap0 state /\
      (∀ptr' u. MEM (Pointer ptr' u) ptr ⇒ ptr' < heap_length state.heap) ∧
      (heap_length state.heap = conf.limit) /\
      (gen_gc$gc_move_list
         (to_gen_conf conf)
         (to_gen_state conf state)
         (MAP (to_gen_heap_address conf) ptr) = (ptr1', state1')) /\ state1'.ok ==>
      sim_inv conf heap0 state' /\
      ((ptr1', state1')
       = (MAP (to_gen_heap_address conf) ptr', to_gen_state conf state')) /\
      all_old_ptrs conf ptr' SUBSET all_old_ptrs conf ptr``;
val _ = replay "gc_move_simulation_typed" ``!ptr ptr' state state' ptr1' state1'.
      (gc_move conf state ptr = (ptr', state')) /\
      (!ptr' u. (ptr = Pointer ptr' u) ==>  ptr' < heap_length state.heap) /\
      (heap_length state.heap = conf.limit) /\
      sim_inv conf heap0 state /\
      (gen_gc$gc_move
         (to_gen_conf conf)
         (to_gen_state conf state)
         (to_gen_heap_address conf ptr) = (ptr1', state1')) /\ state1'.ok ==>
      sim_inv conf heap0 state' /\
      ((ptr1', state1')
       = (to_gen_heap_address conf ptr', to_gen_state conf state')) /\
      all_old_ptrs conf [ptr'] SUBSET all_old_ptrs conf [ptr]``;
