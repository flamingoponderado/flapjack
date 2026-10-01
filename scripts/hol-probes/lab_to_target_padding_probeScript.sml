(* Direct HOL-EVAL observations for the lab_to_target label-checking, padding
   and symbol-collection definitions (lab_to_targetScript.sml:168-245):
   line_ok_light, sec_ok_light, pad_bytes, add_nop, pad_section, pad_code,
   sec_length and get_symbols.  Bead flapjack-pxn.18.5.15.10.14.

   All line/section inputs are concrete 64-bit labLang$line/labLang$sec values.
   The assembler configuration is an 8-bit record with code_alignment 2,
   jump/cjump/loc offset bounds (0,100), avoid_regs [3] and reg_count 8, so a
   jump target 8w is in range and two-aligned (T) while 3w is unaligned and
   101w is out of range (both F); Call is unconditionally rejected.

   Rows: pad_bytes when len fits, appends with one repeating byte, and appends
   with a two-byte nop chunk; add_nop empty, Label-then-Asm (the Asm clause
   stops recursion), Asm head and LabAsm head; pad_section empty and a
   Label/Asm/Label list where the second Label triggers add_nop; pad_code empty
   and two sections; sec_length empty and a concrete line list; get_symbols
   empty and two sections; the ten line_ok_light shapes and two sec_ok_light
   sections. *)

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

(* Bytes and nop chunks *)
val _ = print_eval "PadBytesFits" ``pad_bytes [1w;2w;3w] 2 [9w]``;
val _ = print_eval "PadBytesAppend" ``pad_bytes [1w;2w] 3 [9w]``;
val _ = print_eval "PadBytesLonger" ``pad_bytes [1w] 3 [9w;8w]``;

val addNopLines = ``[labLang$Label 1 2 3;
                     labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w;2w] 2;
                     labLang$Label 4 5 6] : 64 labLang$line list``;
val _ = print_eval "AddNopEmpty" ``add_nop [7w] ([] : 64 labLang$line list)``;
val _ = print_eval "AddNopLabelThenAsm" ``add_nop [7w] ^addNopLines``;
val _ = print_eval "AddNopAsmHead"
  ``add_nop [7w]
      ([labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w] 1;
        labLang$Label 9 9 9] : 64 labLang$line list)``;
val _ = print_eval "AddNopLabAsmHead"
  ``add_nop [7w]
      ([labLang$LabAsm (labLang$Jump (labLang$Lab 1 2))
          (0w:64 word) [1w] 1;
        labLang$Label 9 9 9] : 64 labLang$line list)``;

val padLines = ``[labLang$Label 1 2 0;
                  labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w;2w] 3;
                  labLang$Label 4 5 2] : 64 labLang$line list``;
val _ = print_eval "PadSectionEmpty"
  ``pad_section [9w] ([] : 64 labLang$line list)
      ([labLang$Label 1 2 3] : 64 labLang$line list)``;
val _ = print_eval "PadSectionConcrete" ``pad_section [9w] ^padLines []``;

val secOne = ``labLang$Section 1
   [labLang$Label 1 2 0;
    labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w;2w] 3]
   : 64 labLang$sec``;
val secTwo = ``labLang$Section 2 ([] : 64 labLang$line list) : 64 labLang$sec``;
val _ = print_eval "PadCodeEmpty" ``pad_code [9w] ([] : 64 labLang$sec list)``;
val _ = print_eval "PadCodeTwo"
  ``pad_code [9w] [^secOne; ^secTwo]``;

val _ = print_eval "SecLengthEmpty"
  ``sec_length ([] : 64 labLang$line list) 5``;
val _ = print_eval "SecLengthConcrete" ``sec_length ^addNopLines 10``;

val symSecs = ``[labLang$Section 1 ^addNopLines;
                 labLang$Section 2
                   [labLang$Label 7 8 1;
                    labLang$LabAsm (labLang$Jump (labLang$Lab 1 2))
                      (0w:64 word) [1w] 2]] : 64 labLang$sec list``;
val _ = print_eval "GetSymbolsEmpty"
  ``get_symbols 10 ([] : 64 labLang$sec list)``;
val _ = print_eval "GetSymbolsTwo" ``get_symbols 10 ^symSecs``;

val _ = print_eval "LineOkLightLabel"
  ``line_ok_light ^cfg (labLang$Label 1 2 3)``;
val _ = print_eval "LineOkLightAsm"
  ``line_ok_light ^cfg
      (labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w] 1)``;
val _ = print_eval "LineOkLightHaltOk"
  ``line_ok_light ^cfg (labLang$LabAsm labLang$Halt (8w:64 word) [] 0)``;
val _ = print_eval "LineOkLightHaltBad"
  ``line_ok_light ^cfg (labLang$LabAsm labLang$Halt (3w:64 word) [] 0)``;
val _ = print_eval "LineOkLightInstall"
  ``line_ok_light ^cfg (labLang$LabAsm labLang$Install (8w:64 word) [] 0)``;
val _ = print_eval "LineOkLightCallFFIOk"
  ``line_ok_light ^cfg
      (labLang$LabAsm
        (labLang$CallFFI (strlit "x") : 64 labLang$asm_with_lab)
        (8w:64 word) [] 0)``;
val _ = print_eval "LineOkLightCall"
  ``line_ok_light ^cfg
      (labLang$LabAsm (labLang$Call (labLang$Lab 1 2)) (8w:64 word) [] 0)``;
val _ = print_eval "LineOkLightJumpCmpOk"
  ``line_ok_light ^cfg
      (labLang$LabAsm
        (labLang$JumpCmp asm$Equal 2 (asm$Imm (1w:64 word)) (labLang$Lab 1 2))
        (8w:64 word) [] 0)``;
val _ = print_eval "LineOkLightJumpCmpBad"
  ``line_ok_light ^cfg
      (labLang$LabAsm
        (labLang$JumpCmp asm$Equal 2 (asm$Imm (1w:64 word)) (labLang$Lab 1 2))
        (101w:64 word) [] 0)``;
val _ = print_eval "LineOkLightLocValue"
  ``line_ok_light ^cfg
      (labLang$LabAsm (labLang$LocValue 2 (labLang$Lab 1 2))
        (8w:64 word) [] 0)``;

val _ = print_eval "SecOkLightMixed"
  ``sec_ok_light ^cfg
      (labLang$Section 1
        [labLang$Label 1 2 3;
         labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w] 1;
         labLang$LabAsm labLang$Halt (8w:64 word) [] 0])``;
val _ = print_eval "SecOkLightCall"
  ``sec_ok_light ^cfg
      (labLang$Section 1
        [labLang$LabAsm (labLang$Call (labLang$Lab 1 2))
          (8w:64 word) [] 0])``;
