load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
val _ = show_type "value_number_type=" ``dataSem$Number``;
val _ = show_type "value_word64_type=" ``dataSem$Word64``;
val _ = show_type "value_block_type=" ``dataSem$Block``;
val _ = show_type "value_code_ptr_type=" ``dataSem$CodePtr``;
val _ = show_type "value_ref_ptr_type=" ``dataSem$RefPtr``;
val _ = show_type "thunk_bad_ref_type=" ``dataSem$BadRef``;
val _ = show_type "thunk_not_thunk_type=" ``dataSem$NotThunk``;
val _ = show_type "thunk_is_thunk_type=" ``dataSem$IsThunk``;
val _ = show "bool_value=" dataSemTheory.Boolv_def;
val _ = show "unit_value=" dataSemTheory.Unit_def;
val _ = show "value_to_list=" dataSemTheory.v_to_list_def;
val _ = show "list_to_value=" dataSemTheory.list_to_v_def;
val _ = show "with_fresh_timestamp=" dataSemTheory.with_fresh_ts_def;
val _ = show "check_limit=" dataSemTheory.check_lim_def;
val _ = show "dest_bool=" dataSemTheory.dest_Boolv_def;
val _ = show "dest_thunk=" dataSemTheory.dest_thunk_def;
val _ = show "bad_thunk_update=" dataSemTheory.bad_thunk_update_def;
val _ = show "is_closure=" dataSemTheory.isClos_def;
val _ = show "value_equality=" dataSemTheory.do_eq_def;
val _ = show "integer_application=" dataSemTheory.do_int_app_def;
val _ = show "word_application=" dataSemTheory.do_word_app_def;
val _ = show "build_part=" dataSemTheory.do_part_def;
val _ = show "build_sequence=" dataSemTheory.do_build_def;
val _ = show "build_constant=" dataSemTheory.do_build_const_def;
val _ = show "finalise_cons=" dataSemTheory.finalise_cons_def;
val _ = show "do_app_aux=" dataSemTheory.do_app_aux_def;
val _ = show "nullary_cons=" (EVAL ``dataSem$do_app_aux (closLang$BlockOp (closLang$Cons 9)) []
  (s:('c,'ffi) dataSem$state)``);
val _ = show "nonempty_cons=" (EVAL ``dataSem$do_app_aux (closLang$BlockOp (closLang$Cons 9))
  [dataSem$Number 4] ((s:('c,'ffi) dataSem$state) with tstamps := SOME 7)``);
val _ = show "invalid_list_length=" (EVAL ``dataSem$do_app_aux (closLang$BlockOp (closLang$FromList 9))
  [dataSem$Number 1; dataSem$Block 0 backend_common$nil_tag []] (s:('c,'ffi) dataSem$state)``);
val _ = show "integer_add=" (EVAL ``dataSem$do_app_aux (closLang$IntOp closLang$Add)
  [dataSem$Number 4; dataSem$Number 7] (s:('c,'ffi) dataSem$state)``);
val _ = show "unsupported_copy=" (EVAL ``dataSem$do_app_aux (closLang$MemOp (closLang$CopyByte T))
  [] (s:('c,'ffi) dataSem$state)``);
