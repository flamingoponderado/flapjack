(* Direct HOL-EVAL observations for the lab_to_target zero-label accumulation
   and label-removal definitions (lab_to_targetScript.sml:248-337):
   zero_labs_acc_of, line_get_zero_labs_acc, sec_get_zero_labs_acc,
   get_zero_labs_acc, zero_labs_acc_exist, remove_labels_loop, remove_labels,
   line_bytes and prog_to_bytes.  Bead flapjack-pxn.18.5.15.10.16.

   The accumulator observations print `toAList` of the resulting `num_set` so
   the tree shapes are compared as association lists.  All line/section inputs
   are concrete 64-bit labLang$line/labLang$sec values and the assembler
   configuration is the 8/64 record used by the sibling padding probe
   (code_alignment 2, offset bounds (0,100), avoid_regs [3], reg_count 8). *)

load "bossLib";
load "preamble";
load "lab_to_targetTheory";
load "asmTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open lab_to_targetTheory;
open asmTheory;

fun print_eval label q =
  let val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

(* zero_labs_acc_of: hit with n2 = 0, non-zero second part, catch-all *)
val _ = print_eval "ZeroLabsAccOfLocHit"
  ``toAList (zero_labs_acc_of (LocValue 2 (Lab 4 0)) (LN : num_set))``;
val _ = print_eval "ZeroLabsAccOfLocNonzero"
  ``toAList (zero_labs_acc_of (LocValue 2 (Lab 4 7)) (LN : num_set))``;
val _ = print_eval "ZeroLabsAccOfJumpHit"
  ``toAList (zero_labs_acc_of (Jump (Lab 6 0)) (LN : num_set))``;
val _ = print_eval "ZeroLabsAccOfJumpNonzero"
  ``toAList (zero_labs_acc_of (Jump (Lab 6 3)) (LN : num_set))``;
val _ = print_eval "ZeroLabsAccOfJumpCmpHit"
  ``toAList (zero_labs_acc_of
      (JumpCmp Equal 2 (Imm (1w:64 word)) (Lab 8 0)) (LN : num_set))``;
val _ = print_eval "ZeroLabsAccOfJumpCmpNonzero"
  ``toAList (zero_labs_acc_of
      (JumpCmp Equal 2 (Imm (1w:64 word)) (Lab 8 9)) (LN : num_set))``;
val _ = print_eval "ZeroLabsAccOfCatchAll"
  ``toAList (zero_labs_acc_of Halt (LN : num_set))``;

(* line_get_zero_labs_acc *)
val labJumpLine =
  ``labLang$LabAsm (labLang$Jump (labLang$Lab 6 0)) (0w:64 word) [] 1``;
val _ = print_eval "LineGetZeroLabsAccLabAsm"
  ``toAList (line_get_zero_labs_acc ^labJumpLine (LN : num_set))``;
val _ = print_eval "LineGetZeroLabsAccLabel"
  ``toAList (line_get_zero_labs_acc (labLang$Label 1 2 3) (LN : num_set))``;
val _ = print_eval "LineGetZeroLabsAccAsm"
  ``toAList (line_get_zero_labs_acc
      (labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w] 1) (LN : num_set))``;

(* get_zero_labs_acc over a small code with two zero labels and one non-zero *)
val zeroCode = ``[labLang$Section 1
   [labLang$Label 1 5 1;
    labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:64 word) [] 1;
    labLang$LabAsm (labLang$Jump (labLang$Lab 1 5)) (0w:64 word) [] 1;
    labLang$LabAsm
      (labLang$JumpCmp asm$Equal 2 (asm$Imm (1w:64 word)) (labLang$Lab 3 0))
      (0w:64 word) [] 1;
    labLang$LabAsm labLang$Halt (0w:64 word) [] 1]] : 64 labLang$sec list``;
val _ = print_eval "GetZeroLabsAccEmpty"
  ``toAList (get_zero_labs_acc ([] : 64 labLang$sec list))``;
val _ = print_eval "GetZeroLabsAccConcrete"
  ``toAList (get_zero_labs_acc ^zeroCode)``;

(* zero_labs_acc_exist: the zero set is {1, 3} *)
val goodLabs =
  ``insert 1 (insert 0 10 LN) (insert 3 (insert 0 10 LN) (LN : num num_map num_map))``;
val badLabs = ``insert 1 (insert 0 10 LN) (LN : num num_map num_map)``;
val _ = print_eval "ZeroLabsAccExistTrue"
  ``zero_labs_acc_exist ^goodLabs ^zeroCode``;
val _ = print_eval "ZeroLabsAccExistFalse"
  ``zero_labs_acc_exist ^badLabs ^zeroCode``;

(* line_bytes / prog_to_bytes *)
val _ = print_eval "LineBytesLabel" ``line_bytes (labLang$Label 1 2 3)``;
val _ = print_eval "LineBytesAsm"
  ``line_bytes (labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w;2w] 2)``;
val _ = print_eval "LineBytesLabAsm"
  ``line_bytes ^labJumpLine``;

val bytesCode = ``[labLang$Section 1
    [labLang$Label 1 2 3;
     labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w;2w] 2];
   labLang$Section 2 ([] : 64 labLang$line list);
   labLang$Section 3
    [labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:64 word) [3w] 1]]
   : 64 labLang$sec list``;
val _ = print_eval "ProgToBytesEmpty"
  ``prog_to_bytes ([] : 64 labLang$sec list)``;
val _ = print_eval "ProgToBytesConcrete" ``prog_to_bytes ^bytesCode``;

(* assembler configuration with an encoder that discards its argument *)
val cfg = ``<| ISA := RISC_V
   ; encode := (\x. ([] : word8 list))
   ; big_endian := F
   ; code_alignment := 2
   ; link_reg := NONE
   ; avoid_regs := [3]
   ; reg_count := 8
   ; fp_reg_count := 4
   ; two_reg_arith := T
   ; valid_imm := (K (K T))
   ; addr_offset := (0w, 100w)
   ; hw_offset := (0w, 100w)
   ; byte_offset := (0w, 100w)
   ; jump_offset := (0w, 100w)
   ; cjump_offset := (0w, 100w)
   ; loc_offset := (0w, 100w)
   |> : 64 asm_config``;

(* label-removal loop over a one-section program and its seeding wrapper *)
val loopCode = ``[labLang$Section 1
   [labLang$Label 1 5 1;
    labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:64 word) [] 1]]
   : 64 labLang$sec list``;
val _ = print_eval "RemoveLabelsLoopZero"
  ``remove_labels_loop 0 ^cfg 10 (LN : num num_map num_map) [] ^loopCode``;
val _ = print_eval "RemoveLabelsLoopOne"
  ``remove_labels_loop 1 ^cfg 10 (LN : num num_map num_map) [] ^loopCode``;
val _ = print_eval "RemoveLabelsZero"
  ``remove_labels 0 ^cfg 10 (LN : num num_map num_map) [] ^loopCode``;
