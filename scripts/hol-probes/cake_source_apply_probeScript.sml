load "semanticPrimitivesTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun capture name tm =
  let val result = rhs (concl (CONV_RULE (RAND_CONV (DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))) (EVAL tm)))
  in print (name ^ "="); print_term result; print "\n" end;
val _ = capture "ref_alloc" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([Refv (Litv (IntLit 5))], (ARB:num ffi$ffi_state)) Opref [Litv (IntLit 7)])``;
val _ = capture "ref_assign" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([Refv (Litv (IntLit 5))], (ARB:num ffi$ffi_state)) Opassign [Loc F 0; Litv (IntLit 7)])``;
val _ = capture "ref_invalid" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([Refv (Litv (IntLit 5))], (ARB:num ffi$ffi_state)) Opderef [Loc T 1])``;
val _ = capture "ref_wrong_type" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array []], (ARB:num ffi$ffi_state)) Opassign [Loc T 0; Litv (IntLit 7)])``;
val _ = capture "list_append" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) ListAppend [list_to_v [Litv (IntLit 1)]; list_to_v [Litv (IntLit 2)]])``;
val _ = capture "shift8" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) (Shift W8 Lsl 2) [Litv (Word8 7w)])``;
val _ = capture "eq_mismatch" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) Equality [Litv (IntLit 7); Litv (Word8 7w)])``;
val _ = capture "byte_alloc" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) Aw8alloc [Litv (IntLit 2); Litv (Word8 7w)])``;
val _ = capture "byte_negative" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) Aw8alloc [Litv (IntLit (-1)); Litv (Word8 7w)])``;
val _ = capture "byte_read" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [4w;7w]], (ARB:num ffi$ffi_state)) Aw8sub [Loc F 0; Litv (IntLit 1)])``;
val _ = capture "byte_safe_oob" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [4w;7w]], (ARB:num ffi$ffi_state)) Aw8sub [Loc T 0; Litv (IntLit 2)])``;
val _ = capture "byte_unsafe_oob" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [4w;7w]], (ARB:num ffi$ffi_state)) Aw8sub_unsafe [Loc T 0; Litv (IntLit 2)])``;
val _ = capture "byte_update" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [4w;7w]], (ARB:num ffi$ffi_state)) Aw8update [Loc T 0; Litv (IntLit 1); Litv (Word8 9w)])``;
val _ = capture "array_fixed" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) AallocFixed [Litv (IntLit 4); Litv (IntLit 7)])``;
val _ = capture "array_update" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([Varray [Litv (IntLit 4); Litv (IntLit 7)]], (ARB:num ffi$ffi_state)) Aupdate [Loc F 0; Litv (IntLit 1); Litv (IntLit 9)])``;
val _ = capture "array_negative" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([Varray [Litv (IntLit 4)]], (ARB:num ffi$ffi_state)) Asub [Loc T 0; Litv (IntLit (-1))])``;
val _ = capture "vector_unsafe" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) Vsub_unsafe [Vectorv [Litv (IntLit 4)]; Litv (IntLit (-1))])``;
val _ = capture "substring" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) CopyStrStr [Litv (StrLit «abcd»); Litv (IntLit 1); Litv (IntLit 2)])``;
val _ = capture "substring_oob" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) CopyStrStr [Litv (StrLit «abcd»); Litv (IntLit 3); Litv (IntLit 2)])``;
val _ = capture "byte_copy_overlap" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [1w;2w;3w;4w]], (ARB:num ffi$ffi_state)) CopyAw8Aw8
    [Loc T 0; Litv (IntLit 0); Litv (IntLit 3); Loc F 0; Litv (IntLit 1)])``;
val _ = capture "string_copy_byte" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [0w;0w;0w]], (ARB:num ffi$ffi_state)) CopyStrAw8
    [Litv (StrLit «abc»); Litv (IntLit 1); Litv (IntLit 2); Loc T 0; Litv (IntLit 1)])``;
val _ = capture "byte_xor" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [1w;2w;3w]], (ARB:num ffi$ffi_state)) XorAw8Str_unsafe
    [Loc F 0; Litv (StrLit «AB»)])``;
val _ = capture "byte_xor_short" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [1w]], (ARB:num ffi$ffi_state)) XorAw8Str_unsafe
    [Loc T 0; Litv (StrLit «AB»)])``;
val _ = capture "string_sub_negative" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) Strsub [Litv (StrLit «abc»); Litv (IntLit (-1))])``;
val _ = capture "env_id" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) Env_id [Conv NONE [Litv (IntLit 5); Litv (IntLit 9)]])``;
val _ = capture "ffi_empty" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([W8array [1w;2w]], (ARB:num ffi$ffi_state)) (FFI «») [Litv (StrLit «x»); Loc T 0])``;
val _ = capture "thunk_alloc" ``OPTION_MAP (λ(x,r). (FST x,r))
  (do_app ([], (ARB:num ffi$ffi_state)) (ThunkOp (AllocThunk NotEvaluated)) [Litv (IntLit 5)])``;
val _ = capture "ffi_return" ``OPTION_MAP (λ(x,r). (FST x, (SND x).ffi_state, (SND x).io_events, r))
  (do_app ([W8array [1w]],
    (ARB:num ffi$ffi_state) with <|oracle := (λn st conf bytes. Oracle_return (st+1) [9w]); ffi_state := 41; io_events := []|>)
    (FFI «test») [Litv (StrLit «x»); Loc T 0])``;
val _ = capture "ffi_final" ``OPTION_MAP (λ(x,r). (FST x, (SND x).ffi_state, (SND x).io_events, r))
  (do_app ([W8array [1w]],
    (ARB:num ffi$ffi_state) with <|oracle := (λn st conf bytes. Oracle_final FFI_failed); ffi_state := 41; io_events := []|>)
    (FFI «test») [Litv (StrLit «x»); Loc T 0])``;
