(* Direct HOL-EVAL observations for the lab_to_target position, label, FFI-index
   and jump-offset definitions (lab_to_targetScript.sml:86-118): find_pos,
   get_label, get_ffi_index and get_jump_offset.  Bead
   flapjack-pxn.18.5.15.10.11.

   labs maps section 7 to the inner label map {0 -> 10, 3 -> 13}: find_pos of
   Lab 7 3 is 13, of Lab 7 0 is 10, of the missing label Lab 7 9 and of the
   missing section Lab 5 3 is the 0 default.  get_label is observed on all four
   label-carrying constructors and on the Halt default.  ffis = [ExtCall a;
   ExtCall b] gives get_ffi_index (ExtCall b) = 1 (hit) and get_ffi_index
   (ExtCall c) = 0 (default).  get_jump_offset is observed at 64-bit on
   CallFFI b (index 1), Install, Halt and Jump (Lab 7 3), with pos = 10. *)

load "bossLib";
load "preamble";
load "lab_to_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open lab_to_targetTheory;

fun print_eval label q =
  let val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

val labs = ``insert 7 (insert 0 10 (insert 3 13 LN)) LN : num spt spt``;
val ffis = ``[ExtCall (strlit "a"); ExtCall (strlit "b")] : ffiname list``;

val _ = print_eval "FindPosHit" ``find_pos (labLang$Lab 7 3) ^labs``;
val _ = print_eval "FindPosHitZero" ``find_pos (labLang$Lab 7 0) ^labs``;
val _ = print_eval "FindPosDefaultLabel" ``find_pos (labLang$Lab 7 9) ^labs``;
val _ = print_eval "FindPosDefaultSection" ``find_pos (labLang$Lab 5 3) ^labs``;

val _ = print_eval "GetLabelJump"
  ``get_label ((labLang$Jump (labLang$Lab 1 2)) : unit labLang$asm_with_lab)``;
val _ = print_eval "GetLabelJumpCmp"
  ``get_label ((labLang$JumpCmp asm$Equal 0 (asm$Reg 0) (labLang$Lab 3 4)) :
      unit labLang$asm_with_lab)``;
val _ = print_eval "GetLabelCall"
  ``get_label ((labLang$Call (labLang$Lab 5 6)) : unit labLang$asm_with_lab)``;
val _ = print_eval "GetLabelLocValue"
  ``get_label ((labLang$LocValue 7 (labLang$Lab 8 9)) : unit labLang$asm_with_lab)``;
val _ = print_eval "GetLabelDefault"
  ``get_label (labLang$Halt : unit labLang$asm_with_lab)``;

val _ = print_eval "GetFfiIndexHit" ``get_ffi_index ^ffis (ExtCall (strlit "b"))``;
val _ = print_eval "GetFfiIndexDefault" ``get_ffi_index ^ffis (ExtCall (strlit "c"))``;

val _ = print_eval "GetJumpOffsetCallFFI"
  ``(get_jump_offset ((labLang$CallFFI (strlit "b")) : unit labLang$asm_with_lab)
      ^ffis ^labs 10) : 64 word``;
val _ = print_eval "GetJumpOffsetInstall"
  ``(get_jump_offset (labLang$Install : unit labLang$asm_with_lab) ^ffis ^labs 10)
      : 64 word``;
val _ = print_eval "GetJumpOffsetHalt"
  ``(get_jump_offset (labLang$Halt : unit labLang$asm_with_lab) ^ffis ^labs 10)
      : 64 word``;
val _ = print_eval "GetJumpOffsetJump"
  ``(get_jump_offset ((labLang$Jump (labLang$Lab 7 3)) : unit labLang$asm_with_lab)
      ^ffis ^labs 10) : 64 word``;
