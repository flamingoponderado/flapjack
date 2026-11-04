load "copying_gcTheory";
open HolKernel Parse boolLib bossLib gc_sharedTheory copying_gcTheory;
val _ = Globals.linewidth := 1000000;
fun show label th =
  if null (hyp th) then
    (print label; print "="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "gc_forward_ptr_typed" gc_forward_ptr_def;
val _ = show "gc_forward_ptr_thm_typed" gc_forward_ptr_thm;
val _ = show "gc_move_typed" gc_move_def;
val _ = show "gc_move_list_typed" gc_move_list_def;
val _ = show "gc_move_loop_typed" gc_move_loop_def;
val _ = show "full_gc_typed" full_gc_def;
val _ = show "gc_move_list_repeat" (SIMP_RULE (srw_ss()) [isDataElement_def] (EVAL ``gc_move_list
  ([Pointer 0 (9:num); Pointer 0 10], [], 0, 2, [DataElement [] 1 (4:num)], T, 2)``));
val _ = show "full_gc_data" (EVAL ``full_gc
  ([Data (7:num)], [Unused 1 : (num,num) heap_element], 2)``);
val _ = show "full_gc_pointer" (SIMP_RULE (srw_ss()) [isDataElement_def] (EVAL ``full_gc
  ([Pointer 0 (9:num)], [DataElement [Data 5] 1 (4:num)], 2)``));
val _ = show "gc_forward_ptr_ok_typed" gc_forward_ptr_ok;
val _ = show "gc_move_ok_typed" gc_move_ok;
val _ = show "gc_move_list_ok_typed" gc_move_list_ok;
val _ = show "gc_move_loop_ok_typed" gc_move_loop_ok;
val _ = show "gc_move_list_IMP_LENGTH_typed" gc_move_list_IMP_LENGTH;
val _ = show "full_gc_IMP_LENGTH_typed" full_gc_IMP_LENGTH;
val _ = show "gc_move_IMP_isDataElement_typed" gc_move_IMP_isDataElement;
val _ = show "gc_move_list_IMP_isDataElement_typed" gc_move_list_IMP_isDataElement;
val _ = show "gc_move_loop_IMP_isDataElement_typed" gc_move_loop_IMP_isDataElement;
val _ = show "full_gc_IMP_isDataElement_typed" full_gc_IMP_isDataElement;
