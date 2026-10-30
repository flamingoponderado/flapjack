(* Original BVL runtime carriers, primitive definitions and representative results. *)
load "clos_to_bvlProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun typ label term = (print label; print_type (type_of term); print "\n");
fun example label term = (print label; print_term (rhs (concl (EVAL term))); print "\n");
val _ = typ "value_array_type=" ``bvlSem$ValueArray``;
val _ = typ "byte_array_type=" ``bvlSem$ByteArray``;
val _ = typ "thunk_type=" ``bvlSem$Thunk``;
val _ = typ "mut_block_type=" ``bvlSem$MutBlock``;
val _ = typ "number_type=" ``bvlSem$Number``;
val _ = typ "word_type=" ``bvlSem$Word64``;
val _ = typ "block_type=" ``bvlSem$Block``;
val _ = typ "code_ptr_type=" ``bvlSem$CodePtr``;
val _ = typ "ref_ptr_type=" ``bvlSem$RefPtr``;
val _ = show "bool_value=" bvlSemTheory.Boolv_def;
val _ = show "unit_value=" bvlSemTheory.Unit_def;
val _ = show "value_to_list=" bvlSemTheory.v_to_list_def;
val _ = show "list_to_value=" bvlSemTheory.list_to_v_def;
val _ = show "is_closure=" bvlSemTheory.isClos_def;
val _ = show "int_app=" bvlSemTheory.do_int_app_def;
val _ = show "add_args=" clos_to_bvlProofTheory.add_args_def;
val _ = show "get_num_args=" clos_to_bvlProofTheory.get_num_args_def;
val _ = typ "int_app_type=" ``bvlSem$do_int_app``;
val _ = example "negative_div=" ``bvlSem$do_int_app closLang$Div [bvlSem$Number (~10); bvlSem$Number 3]``;
val _ = example "negative_mod=" ``bvlSem$do_int_app closLang$Mod [bvlSem$Number (~10); bvlSem$Number 3]``;
val _ = example "negative_divisor_div=" ``bvlSem$do_int_app closLang$Div [bvlSem$Number 10; bvlSem$Number (~3)]``;
val _ = example "negative_divisor_mod=" ``bvlSem$do_int_app closLang$Mod [bvlSem$Number 10; bvlSem$Number (~3)]``;
val _ = example "zero_div=" ``bvlSem$do_int_app closLang$Div [bvlSem$Number 1; bvlSem$Number 0]``;
val _ = example "list_roundtrip=" ``bvlSem$v_to_list (bvlSem$list_to_v [bvlSem$Number 1; bvlSem$Number 2])``;
val _ = example "bad_list=" ``bvlSem$v_to_list (bvlSem$Block 1 [])``;
val _ = show "do_eq=" bvlSemTheory.do_eq_def;
val _ = typ "do_eq_type=" ``bvlSem$do_eq``;
val _ = typ "do_eq_list_type=" ``bvlSem$do_eq_list``;
val _ = example "eq_bytes=" ``bvlSem$do_eq
  (FEMPTY |+ (1,bvlSem$ByteArray T [5w;6w]) |+ (2,bvlSem$ByteArray T [5w;6w]))
  (bvlSem$RefPtr T 1) (bvlSem$RefPtr T 2)``;
val _ = example "eq_bytes_vs_ref=" ``bvlSem$do_eq
  (FEMPTY |+ (1,bvlSem$ByteArray T [5w]) |+ (2,bvlSem$ByteArray F [5w]))
  (bvlSem$RefPtr T 1) (bvlSem$RefPtr T 2)``;
val _ = example "eq_closures=" ``bvlSem$do_eq FEMPTY
  (bvlSem$Block 30 [bvlSem$CodePtr 3]) (bvlSem$Block 31 [bvlSem$Number 4])``;
val _ = example "eq_codeptr=" ``bvlSem$do_eq FEMPTY (bvlSem$CodePtr 1) (bvlSem$CodePtr 1)``;
val _ = example "eq_shortcircuit=" ``bvlSem$do_eq_list FEMPTY
  [bvlSem$Number 1; bvlSem$CodePtr 0] [bvlSem$Number 2; bvlSem$CodePtr 0]``;
val _ = typ "state_globals_type=" ``λ(s:('c,'ffi) bvlSem$state). s.globals``;
val _ = typ "state_refs_type=" ``λ(s:('c,'ffi) bvlSem$state). s.refs``;
val _ = typ "state_clock_type=" ``λ(s:('c,'ffi) bvlSem$state). s.clock``;
val _ = typ "state_compile_type=" ``λ(s:('c,'ffi) bvlSem$state). s.compile``;
val _ = typ "state_oracle_type=" ``λ(s:('c,'ffi) bvlSem$state). s.compile_oracle``;
val _ = typ "state_code_type=" ``λ(s:('c,'ffi) bvlSem$state). s.code``;
val _ = typ "state_ffi_type=" ``λ(s:('c,'ffi) bvlSem$state). s.ffi``;
val _ = show "dec_clock=" bvlSemTheory.dec_clock_def;
val _ = show "initial_state=" bvlSemTheory.initial_state_def;
val _ = show "find_code=" bvlSemTheory.find_code_def;
val _ = typ "find_code_type=" ``bvlSem$find_code``;
val _ = example "direct_call=" ``bvlSem$find_code (SOME 4) [bvlSem$Number 10; bvlSem$Number 20]
  (sptree$insert 4 (2,bvl$Var 3) sptree$LN)``;
val _ = example "indirect_call=" ``bvlSem$find_code NONE [bvlSem$Number 10; bvlSem$Number 20; bvlSem$CodePtr 4]
  (sptree$insert 4 (2,bvl$Var 3) sptree$LN)``;
val _ = example "indirect_bad_arity=" ``bvlSem$find_code NONE [bvlSem$Number 10; bvlSem$CodePtr 4]
  (sptree$insert 4 (2,bvl$Var 3) sptree$LN)``;
val _ = example "indirect_bad_pointer=" ``bvlSem$find_code NONE [bvlSem$Number 4]
  (sptree$insert 4 (0,bvl$Var 3) sptree$LN)``;
val _ = example "indirect_empty=" ``bvlSem$find_code NONE [] (sptree$LN : (num # bvl$exp) sptree$num_map)``;
val _ = show "dest_thunk=" bvlSemTheory.dest_thunk_def;
val _ = typ "dest_thunk_type=" ``bvlSem$dest_thunk``;
val _ = show "bad_thunk_update=" bvlSemTheory.bad_thunk_update_def;
val _ = typ "is_thunk_type=" ``bvlSem$IsThunk``;
val _ = example "thunk_good=" ``bvlSem$dest_thunk (bvlSem$RefPtr F 1)
  (FEMPTY |+ (1,bvlSem$Thunk Evaluated (bvlSem$Number 7)))``;
val _ = example "thunk_bad_flag=" ``bvlSem$dest_thunk (bvlSem$RefPtr T 1)
  (FEMPTY |+ (1,bvlSem$Thunk Evaluated (bvlSem$Number 7)))``;
val _ = example "thunk_missing=" ``bvlSem$dest_thunk (bvlSem$RefPtr F 1) FEMPTY``;
val _ = example "thunk_nonref=" ``bvlSem$dest_thunk (bvlSem$Number 1) FEMPTY``;
val _ = show "fix_clock=" bvlSemTheory.fix_clock_def;
val _ = typ "fix_clock_type=" ``bvlSem$fix_clock``;
