load "flatSemTheory";
load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val exists_eq = CONV_RULE (DEPTH_CONV ETA_CONV) (prove (``∀a:'a. ∃x. a = x``, metis_tac []));
fun show_int_eval label tm =
  (print label; print_term (rhs (concl (CONV_RULE
    (RAND_CONV (SIMP_CONV (srw_ss()) [boolTheory.EXISTS_REFL, exists_eq] THENC EVAL)) (EVAL tm)))); print "\n");
fun show_word_eval label tm = (print label; print_term (rhs (concl
  ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) THENC EVAL) tm))); print "\n");
val _ = show_thm "do_app_typed=" flatSemTheory.do_app_def;
val _ = show_eval "global_alloc=" ``OPTION_MAP (λ(s,r). (s.globals,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := []) (GlobalVarAlloc 2) [])``;
val _ = show_eval "global_init=" ``OPTION_MAP (λ(s,r). (s.globals,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [NONE]) (GlobalVarInit 0) [Litv (IntLit 7)])``;
val _ = show_eval "global_reinit=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [SOME (Litv (IntLit 3))]) (GlobalVarInit 0) [Litv (IntLit 7)])``;
val _ = show_eval "global_lookup=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [SOME (Litv (IntLit 7))]) (GlobalVarLookup 0) [])``;
val _ = show_eval "global_missing=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [NONE]) (GlobalVarLookup 0) [])``;
val _ = show_eval "tag_match=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (TagLenEq 2 1) [Conv (SOME (2,NONE)) [Litv (IntLit 7)]])``;
val _ = show_eval "tag_mismatch=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (TagLenEq 3 1) [Conv (SOME (2,NONE)) [Litv (IntLit 7)]])``;
val _ = show_eval "tuple_length=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (LenEq 1) [Conv NONE [Litv (IntLit 7)]])``;
val _ = show_eval "field_index=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (El 0) [Conv NONE [Litv (IntLit 7)]])``;
val _ = show_eval "ref_field=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 7))]) (El 0) [Loc T 0])``;
val _ = show_eval "ref_bad_index=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 7))]) (El 1) [Loc T 0])``;
val _ = show_eval "identity=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) Id [Litv (IntLit 7)])``;
val _ = show_eval "ref_alloc=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 2))])
    (Src Opref) [Litv (IntLit 7)])``;
val _ = show_eval "ref_assign=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 2))])
    (Src Opassign) [Loc T 0; Litv (IntLit 7)])``;
val _ = show_eval "byte_safe_oob=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w]])
    (Src Aw8sub) [Loc T 0; Litv (IntLit 2)])``;
val _ = show_eval "byte_unsafe_oob=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w]])
    (Src Aw8sub_unsafe) [Loc T 0; Litv (IntLit 2)])``;
val _ = show_eval "array_negative=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Aalloc) [Litv (IntLit ~1); Litv (IntLit 7)])``;
val _ = show_eval "array_update=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Varray [Litv (IntLit 2)]])
    (Src Aupdate) [Loc T 0; Litv (IntLit 0); Litv (IntLit 7)])``;
val _ = show_eval "array_wrong_store=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w]])
    (Src Aupdate) [Loc T 0; Litv (IntLit 0); Litv (IntLit 7)])``;
val _ = show_eval "data_strlen=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Strlen) [Litv (StrLit «abc»)])``;
val _ = show_eval "data_strsub_negative=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Strsub) [Litv (StrLit «abc»); Litv (IntLit (-1))])``;
val _ = show_eval "data_vector_sub=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Vsub) [Vectorv [Litv (IntLit 4)]; Litv (IntLit 0)])``;
val _ = show_eval "data_vector_unsafe=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Vsub_unsafe) [Vectorv [Litv (IntLit 4)]; Litv (IntLit 1)])``;
val _ = show_eval "data_copy=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src CopyStrStr) [Litv (StrLit «abcd»); Litv (IntLit 1); Litv (IntLit 2)])``;
val _ = show_eval "data_copy_oob=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src CopyStrStr) [Litv (StrLit «abcd»); Litv (IntLit 3); Litv (IntLit 2)])``;
val _ = show_eval "data_thunk_alloc=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [])
    (Src (ThunkOp (AllocThunk NotEvaluated))) [Litv (IntLit 5)])``;
val _ = show_eval "numeric_shift=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Shift W8 Lsl 2)) [Litv (Word8 7w)])``;
val _ = show_int_eval "numeric_int_div_negative=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Div IntT)) [Litv (IntLit (~7)); Litv (IntLit 3)])``;
val _ = show_int_eval "numeric_int_div_zero=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Div IntT)) [Litv (IntLit 7); Litv (IntLit 0)])``;
val _ = show_int_eval "numeric_int_mod_negative=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Mod IntT)) [Litv (IntLit (~7)); Litv (IntLit 3)])``;
val _ = show_int_eval "numeric_int_div_negative_divisor=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Div IntT)) [Litv (IntLit 7); Litv (IntLit (~3))])``;
val _ = show_int_eval "numeric_int_mod_negative_divisor=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Mod IntT)) [Litv (IntLit 7); Litv (IntLit (~3))])``;
val _ = show_eval "numeric_int_arity=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Add IntT)) [Litv (IntLit 7)])``;
val _ = show_int_eval "numeric_word8_wrap=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Add (WordT W8))) [Litv (Word8 255w); Litv (Word8 1w)])``;
val _ = show_int_eval "numeric_word64_xor=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Xor (WordT W64))) [Litv (Word64 3w); Litv (Word64 5w)])``;
val _ = show_int_eval "numeric_word8_bad_op=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Mul (WordT W8))) [Litv (Word8 3w); Litv (Word8 5w)])``;
val _ = show_int_eval "numeric_word8_bad_width=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Arith Add (WordT W8))) [Litv (Word8 3w); Litv (Word64 5w)])``;
val _ = show_word_eval "numeric_shift64_rotate=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Shift W64 Ror 65)) [Litv (Word64 3w)])``;
val _ = show_eval "numeric_shift_wrong_width=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Shift W8 Lsl 2)) [Litv (Word64 7w)])``;
val _ = show_eval "numeric_equality_true=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Equality) [Litv (IntLit 7); Litv (IntLit 7)])``;
val _ = show_eval "numeric_equality_bad_type=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Equality) [Litv (IntLit 7); Litv (Word8 7w)])``;
val _ = show_eval "numeric_equality_bad_arity=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Equality) [Litv (IntLit 7)])``;
val _ = show_eval "numeric_test_compare=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Test (Compare Lt) IntT)) [Litv (IntLit 7); Litv (IntLit 8)])``;
val _ = show_eval "numeric_test_bad_type=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Test Equal IntT)) [Litv (IntLit 7); Litv (Word8 7w)])``;
val _ = show_eval "data_copy_overlap=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w;2w;3w;4w]])
    (Src CopyAw8Aw8) [Loc T 0; Litv (IntLit 0); Litv (IntLit 3); Loc T 0; Litv (IntLit 1)])``;
val _ = show_word_eval "data_copy_string_to_bytes=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [0w;0w;0w]])
    (Src CopyStrAw8) [Litv (StrLit «ABC»); Litv (IntLit 1); Litv (IntLit 2); Loc T 0; Litv (IntLit 1)])``;
val _ = show_word_eval "data_copy_bytes_to_string=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [0w;65w;255w]])
    (Src CopyAw8Str) [Loc T 0; Litv (IntLit 1); Litv (IntLit 2)])``;
val _ = show_eval "data_copy_negative_dest=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [0w]])
    (Src CopyStrAw8) [Litv (StrLit «A»); Litv (IntLit 0); Litv (IntLit 1); Loc T 0; Litv (IntLit (-1))])``;
val _ = show_eval "data_copy_wrong_store=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 1))])
    (Src CopyAw8Str) [Loc T 0; Litv (IntLit 0); Litv (IntLit 1)])``;
val _ = show_word_eval "data_xor_bytes=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [3w;5w;7w]])
    (Src XorAw8Str_unsafe) [Loc T 0; Litv (StrLit «AB»)])``;
val _ = show_eval "data_xor_short=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [3w]])
    (Src XorAw8Str_unsafe) [Loc T 0; Litv (StrLit «AB»)])``;
val _ = show_eval "data_implode=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Implode)
    [flatSem$list_to_v [Litv (Char #"A"); Litv (Char #"B")]])``;
val _ = show_eval "data_explode=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Explode) [Litv (StrLit «AB»)])``;
val _ = show_eval "data_strcat_bad=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Strcat)
    [flatSem$list_to_v [Litv (StrLit «A»); Litv (IntLit 1)]])``;
val _ = show_eval "data_vector_from_list=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src VfromList)
    [flatSem$list_to_v [Litv (IntLit 1); Litv (IntLit 2)]])``;
val _ = show_eval "data_vector_length=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Vlength)
    [Vectorv [Litv (IntLit 1); Litv (IntLit 2)]])``;
val _ = show_eval "data_append=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src ListAppend)
    [flatSem$list_to_v [Litv (IntLit 1)]; flatSem$list_to_v [Litv (IntLit 2)]])``;
val _ = show_eval "data_config_gc=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src ConfigGC)
    [Litv (IntLit (-3)); Litv (IntLit 7)])``;
val _ = show_eval "data_thunk_update=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Thunk NotEvaluated (Litv (IntLit 1))])
    (Src (ThunkOp (UpdateThunk Evaluated))) [Loc F 0; Litv (IntLit 2)])``;
val _ = show_eval "data_thunk_bad_location=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Thunk NotEvaluated (Litv (IntLit 1))])
    (Src (ThunkOp (UpdateThunk Evaluated))) [Loc T 0; Litv (IntLit 2)])``;
val _ = show_eval "data_ffi_empty=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w;2w]])
    (Src (FFI «»)) [Litv (StrLit «x»); Loc T 0])``;
val _ = show_eval "data_ffi_bad_store=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 1))])
    (Src (FFI «x»)) [Litv (StrLit «»); Loc T 0])``;
