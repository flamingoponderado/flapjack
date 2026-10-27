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
