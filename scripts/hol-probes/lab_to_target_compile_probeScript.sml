(* Direct HOL-EVAL observations for the lab_filter and lab_to_target compile
   definitions: list_subset (miscScript.sml:3092), not_skip/filter_skip
   (lab_filterScript.sml:11/15), config (lab_to_targetScript.sml:358-368),
   compile_lab (lab_to_targetScript.sml:430/453) and compile
   (lab_to_targetScript.sml:478).  Bead flapjack-pxn.18.5.15.10.27.

   All line/section inputs are concrete 64-bit labLang$line/labLang$sec values
   and the assembler configuration is the 8/64 record used by the sibling
   padding/label-removal probes, with an encoder that discards its argument. *)

load "bossLib";
load "preamble";
load "lab_to_targetTheory";
load "lab_filterTheory";
load "miscTheory";
load "asmTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open lab_to_targetTheory;
open lab_filterTheory;
open asmTheory;

fun print_eval label q =
  let val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

(* not_skip: the skip line, another Asm, a Label and a LabAsm *)
val skipLine =
  ``labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w] 1 : 64 labLang$line``;
val constLine =
  ``labLang$Asm (labLang$Asmi (asm$Inst (asm$Const 1 (0w:64 word)))) [] 1
      : 64 labLang$line``;
val labelLine = ``labLang$Label 1 5 1 : 64 labLang$line``;
val jumpLine =
  ``labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:64 word) [] 1
      : 64 labLang$line``;
val _ = print_eval "NotSkipSkip" ``not_skip ^skipLine``;
val _ = print_eval "NotSkipAsm" ``not_skip ^constLine``;
val _ = print_eval "NotSkipLabel" ``not_skip ^labelLine``;
val _ = print_eval "NotSkipLabAsm" ``not_skip ^jumpLine``;

(* filter_skip: empty, one section, two sections *)
val _ = print_eval "FilterSkipEmpty"
  ``filter_skip ([] : 64 labLang$sec list)``;
val _ = print_eval "FilterSkipOne"
  ``filter_skip [labLang$Section 1 [^skipLine; ^jumpLine]]``;
val _ = print_eval "FilterSkipTwo"
  ``filter_skip
      [labLang$Section 1 [^skipLine];
       labLang$Section 2 [^jumpLine; ^skipLine]]``;

(* list_subset: a true and a false instance *)
val _ = print_eval "ListSubsetTrue" ``list_subset [1;2] [2;3;1]``;
val _ = print_eval "ListSubsetFalse" ``list_subset [1] ([] : num list)``;

(* config: the seven field projections *)
val lcfg = ``<| labels := (LN : num num_map num_map)
   ; sec_pos_len := ([] : (num # num # num) list)
   ; pos := 10
   ; init_clock := 0
   ; ffi_names := NONE
   ; shmem_extra := ([] : shmem_info_num list)
   ; hash_size := 0 |>``;
val _ = print_eval "ConfigLabels" ``(^lcfg).labels``;
val _ = print_eval "ConfigSecPosLen" ``(^lcfg).sec_pos_len``;
val _ = print_eval "ConfigPos" ``(^lcfg).pos``;
val _ = print_eval "ConfigInitClock" ``(^lcfg).init_clock``;
val _ = print_eval "ConfigFfiNames" ``(^lcfg).ffi_names``;
val _ = print_eval "ConfigShmemExtra" ``(^lcfg).shmem_extra``;
val _ = print_eval "ConfigHashSize" ``(^lcfg).hash_size``;

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

(* config with no FFI names and a one-section program that remove_labels
   accepts; a CallFFI program with an empty ffi_names subset fails; a Call
   program with init_clock 0 and no remove_labels success returns NONE *)
val lcfgNone = lcfg;
val lcfgFfiEmpty = ``<| labels := (LN : num num_map num_map)
   ; sec_pos_len := ([] : (num # num # num) list)
   ; pos := 10
   ; init_clock := 0
   ; ffi_names := SOME ([] : ffiname list)
   ; shmem_extra := ([] : shmem_info_num list)
   ; hash_size := 0 |>``;
val loopCode = ``[labLang$Section 1
   [labLang$Label 1 5 1; ^jumpLine]] : 64 labLang$sec list``;
val ffiCode = ``[labLang$Section 1
   [labLang$LabAsm (labLang$CallFFI (strlit "foo")) (0w:64 word) [] 1]]
   : 64 labLang$sec list``;
val callCode = ``[labLang$Section 1
   [labLang$LabAsm (labLang$Call (labLang$Lab 0 0)) (0w:64 word) [] 0]]
   : 64 labLang$sec list``;
val _ = print_eval "CompileLabSuccess"
  ``compile_lab ^cfg ^lcfgNone ^loopCode``;
val _ = print_eval "CompileLabFfiSubsetFail"
  ``compile_lab ^cfg ^lcfgFfiEmpty ^ffiCode``;
val _ = print_eval "CompileLabRemoveLabelsNone"
  ``compile_lab ^cfg ^lcfgNone ^callCode``;

(* compile = compile_lab on the filter_skip image of the program *)
val compileSkipCode = ``[labLang$Section 1
   [^skipLine; labLang$Label 1 5 1; ^jumpLine]] : 64 labLang$sec list``;
val _ = print_eval "CompileSkip" ``compile ^cfg ^lcfgNone ^compileSkipCode``;
val _ = print_eval "CompileLabFilterSkip"
  ``compile_lab ^cfg ^lcfgNone (filter_skip ^compileSkipCode)``;
