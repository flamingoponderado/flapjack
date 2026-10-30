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
val _ = show "word_app=" bvlSemTheory.do_word_app_def;
val _ = typ "word_app_type=" ``bvlSem$do_word_app``;
val _ = example "word8_add=" ``bvlSem$do_word_app (closLang$WordOpw W8 Add)
  [bvlSem$Number 255; bvlSem$Number 2]``;
val _ = example "word8_invalid=" ``bvlSem$do_word_app (closLang$WordOpw W8 Add)
  [bvlSem$Number 256; bvlSem$Number 2]``;
val _ = example "word64_to_byte=" ``bvlSem$do_word_app (closLang$WordFromWord T)
  [bvlSem$Word64 (511w:word64)]``;
val _ = example "word64_from_negative=" ``bvlSem$do_word_app closLang$WordFromInt
  [bvlSem$Number (~1)]``;
val _ = show "do_part=" bvlSemTheory.do_part_def;
val _ = show "do_build=" bvlSemTheory.do_build_def;
val _ = show "do_build_const=" bvlSemTheory.do_build_const_def;
val _ = typ "do_part_type=" ``bvlSem$do_part``;
val _ = typ "do_build_type=" ``bvlSem$do_build``;
val _ = example "build_empty=" ``FST (bvlSem$do_build_const [] FEMPTY)``;
val _ = example "build_nested=" ``FST (bvlSem$do_build_const
  [closLang$Int 7; closLang$Int 9; closLang$Con 20 [0;1]] FEMPTY)``;
val _ = example "build_string_value=" ``FST (bvlSem$do_build_const [closLang$Str «ab»] FEMPTY)``;
val _ = example "build_string_ref=" ``FLOOKUP (SND (bvlSem$do_build_const [closLang$Str «ab»] FEMPTY)) 0``;
val _ = example "build_collision_value=" ``FST (bvlSem$do_build_const [closLang$Str «x»]
  (FEMPTY |+ (0,bvlSem$ValueArray [])))``;
val _ = example "build_collision_ref=" ``FLOOKUP (SND (bvlSem$do_build_const [closLang$Str «x»]
  (FEMPTY |+ (0,bvlSem$ValueArray [])))) 1``;
val _ = typ "do_app_type=" ``bvlSem$do_app``;
val base_state = ``((ARB:(unit,unit) bvlSem$state) with
  <|globals := [SOME (bvlSem$Number 10); SOME (bvlSem$Number 20)];
    refs := FEMPTY |+ (0,bvlSem$ValueArray [bvlSem$Number 7; bvlSem$Number 9])|>)``;
val _ = example "app_global=" ``case bvlSem$do_app (closLang$GlobOp (Global 0)) [] ^base_state of
  Rval (v,_) => SOME v | _ => NONE``;
val _ = example "app_global_dynamic=" ``case bvlSem$do_app (closLang$GlobOp (Global 0)) [bvlSem$Number 0] ^base_state of
  Rval (v,_) => SOME v | _ => NONE``;
val _ = example "app_set_overwrite=" ``case bvlSem$do_app (closLang$GlobOp (SetGlobal 0)) [bvlSem$Number 42] ^base_state of
  Rval (_,s) => EL 0 s.globals | _ => NONE``;
val _ = example "app_cons_extend=" ``case bvlSem$do_app (closLang$BlockOp (ConsExtend 3))
  [bvlSem$Block 9 [bvlSem$Number 5; bvlSem$Number 6]; bvlSem$Number 1; bvlSem$Number 1;
   bvlSem$Number 2; bvlSem$Number 4] ^base_state of Rval (v,_) => SOME v | _ => NONE``;
val _ = example "app_array_elem=" ``case bvlSem$do_app (closLang$BlockOp (ElemAt 1))
  [bvlSem$RefPtr T 0] ^base_state of Rval (v,_) => SOME v | _ => NONE``;
val _ = example "app_build=" ``case bvlSem$do_app (closLang$BlockOp (Build [closLang$Int 7; closLang$Con 3 [0]]))
  [] ^base_state of Rval (v,_) => SOME v | _ => NONE``;
val _ = example "app_int=" ``case bvlSem$do_app (closLang$IntOp Add)
  [bvlSem$Number 7; bvlSem$Number 8] ^base_state of Rval (v,_) => SOME v | _ => NONE``;
val byte_state = ``(^base_state with refs := FEMPTY |+
  (2,bvlSem$ByteArray F [1w;2w;3w]) |+ (3,bvlSem$ByteArray T [3w;4w]))``;
val _ = example "app_byte_length=" ``case bvlSem$do_app (closLang$MemOp LengthByte)
  [bvlSem$RefPtr F 2] ^byte_state of Rval (v,_) => SOME v | _ => NONE``;
val _ = example "app_byte_deref=" ``case bvlSem$do_app (closLang$MemOp DerefByte)
  [bvlSem$RefPtr T 2; bvlSem$Number 1] ^byte_state of Rval (v,_) => SOME v | _ => NONE``;
val _ = example "app_byte_update=" ``case bvlSem$do_app (closLang$MemOp UpdateByte)
  [bvlSem$RefPtr F 3; bvlSem$Number 0; bvlSem$Number 255] ^byte_state of
  Rval (_,s) => FLOOKUP s.refs 3 | _ => NONE``;
val _ = example "app_byte_bounds=" ``case bvlSem$do_app (closLang$MemOp (BoundsCheckByte T))
  [bvlSem$RefPtr T 2; bvlSem$Number 3] ^byte_state of Rval (v,_) => SOME v | _ => NONE``;
val _ = typ "evaluate_type=" ``bvlSem$evaluate``;
val _ = example "eval_var=" ``FST (bvlSem$evaluate ([bvl$Var 0], [bvlSem$Number 7], ^base_state))``;
val _ = example "eval_let=" ``FST (bvlSem$evaluate
  ([bvl$Let [bvl$Var 0; bvl$Var 1] (bvl$Var 1)], [bvlSem$Number 7; bvlSem$Number 9], ^base_state))``;
val _ = example "eval_handle=" ``FST (bvlSem$evaluate
  ([bvl$Handle (bvl$Raise (bvl$Var 0)) (bvl$Var 0)], [bvlSem$Number 7], ^base_state))``;
val _ = example "eval_op_reverse=" ``FST (bvlSem$evaluate
  ([bvl$Op (closLang$BlockOp (Cons 4)) [bvl$Var 0; bvl$Var 1]],
   [bvlSem$Number 7; bvlSem$Number 9], ^base_state))``;
val _ = example "eval_tick_timeout=" ``FST (bvlSem$evaluate
  ([bvl$Tick (bvl$Var 0)], [bvlSem$Number 7], ^base_state with clock := 0))``;
val call_state = ``(^base_state with <| clock := 3;
  code := sptree$insert 4 (1,bvl$Var 0) sptree$LN |>)``;
val _ = example "eval_call=" ``FST (bvlSem$evaluate
  ([bvl$Call 1 (SOME 4) [bvl$Var 0]], [bvlSem$Number 7], ^call_state))``;
val _ = example "eval_call_clock=" ``(SND (bvlSem$evaluate
  ([bvl$Call 1 (SOME 4) [bvl$Var 0]], [bvlSem$Number 7], ^call_state))).clock``;
