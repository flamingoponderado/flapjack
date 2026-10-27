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
