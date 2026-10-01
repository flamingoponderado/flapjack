(* Direct HOL-EVAL observations for the lab_to_target assembly encoding
   definitions (lab_to_targetScript.sml:15-61): ffi_offset, lab_inst,
   cbw_to_asm, enc_line, enc_sec and enc_sec_list.

   enc_line/enc_sec/enc_sec_list take the instruction encoder as a parameter,
   so the probe supplies a concrete encoder: `Inst Skip` encodes to [1w] and
   every other asm to [2w;3w].  The distinct lengths make the LENGTH bs fields
   observable. *)
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

(* A fresh polymorphic encoder term per use: `Inst Skip` encodes to [1w] and
   every other asm to [2w;3w].  A single `val enc = ``...``;` would fix the
   word dimension at its first use, so re-quote it each time. *)
fun enc_trm () =
  ``\a : 8 asm. if a = asm$Inst asm$Skip then [1w:word8] else [2w:word8; 3w:word8]``;

val w8 = ``(0w : 8 word)``;
val jumpL = ``(labLang$Jump (labLang$Lab 1 2) : 8 labLang$asm_with_lab)``;
val jumpCmpL = ``(labLang$JumpCmp asm$Equal 1 (asm$Reg 2) (labLang$Lab 3 4) :
  8 labLang$asm_with_lab)``;
val callL = ``(labLang$Call (labLang$Lab 5 6) : 8 labLang$asm_with_lab)``;
val locValueL = ``(labLang$LocValue 7 (labLang$Lab 8 9) : 8 labLang$asm_with_lab)``;
val haltL = ``(labLang$Halt : 8 labLang$asm_with_lab)``;
val installL = ``(labLang$Install : 8 labLang$asm_with_lab)``;
val callFfiL = ``(labLang$CallFFI (strlit "f") : 8 labLang$asm_with_lab)``;

val asmiSkip = ``(labLang$Asmi (asm$Inst asm$Skip) : 8 labLang$asm_or_cbw)``;
val cbwL = ``(labLang$Cbw 1 2 : 8 labLang$asm_or_cbw)``;
val shareMemL =
  ``(labLang$ShareMem asm$Load 2 (asm$Addr 3 0w) : 8 labLang$asm_or_cbw)``;

val labelL = ``(labLang$Label 3 4 99 : 8 labLang$line)``;
val asmSkipL = ``(labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [] 0 : 8 labLang$line)``;
val asmCbwL = ``(labLang$Asm (labLang$Cbw 1 2) [] 0 : 8 labLang$line)``;
val labAsmL = ``(labLang$LabAsm (labLang$Halt : 8 labLang$asm_with_lab) 0w [] 0 :
  8 labLang$line)``;
val secL = ``(labLang$Section 3 [^labelL; ^asmSkipL] : 8 labLang$sec)``;

val _ = print_eval "FFIOffset" ``lab_to_target$ffi_offset``;
val _ = print_eval "LabInstJump" ``lab_to_target$lab_inst ^w8 ^jumpL``;
val _ = print_eval "LabInstJumpCmp" ``lab_to_target$lab_inst ^w8 ^jumpCmpL``;
val _ = print_eval "LabInstCall" ``lab_to_target$lab_inst ^w8 ^callL``;
val _ = print_eval "LabInstLocValue" ``lab_to_target$lab_inst ^w8 ^locValueL``;
val _ = print_eval "LabInstHalt" ``lab_to_target$lab_inst ^w8 ^haltL``;
val _ = print_eval "LabInstInstall" ``lab_to_target$lab_inst ^w8 ^installL``;
val _ = print_eval "LabInstCallFFI" ``lab_to_target$lab_inst ^w8 ^callFfiL``;
val _ = print_eval "CbwToAsmAsmi" ``lab_to_target$cbw_to_asm ^asmiSkip``;
val _ = print_eval "CbwToAsmCbw" ``lab_to_target$cbw_to_asm ^cbwL``;
val _ = print_eval "CbwToAsmShareMem" ``lab_to_target$cbw_to_asm ^shareMemL``;
val _ = print_eval "EncLineLabel" ``lab_to_target$enc_line ^(enc_trm ()) 7 ^labelL``;
val _ = print_eval "EncLineAsm" ``lab_to_target$enc_line ^(enc_trm ()) 7 ^asmSkipL``;
val _ = print_eval "EncLineAsmCbw" ``lab_to_target$enc_line ^(enc_trm ()) 7 ^asmCbwL``;
val _ = print_eval "EncLineLabAsm" ``lab_to_target$enc_line ^(enc_trm ()) 7 ^labAsmL``;
val _ = print_eval "EncSec" ``lab_to_target$enc_sec ^(enc_trm ()) 7 ^secL``;
val _ = print_eval "EncSecList" ``lab_to_target$enc_sec_list ^(enc_trm ()) [^secL]``;
