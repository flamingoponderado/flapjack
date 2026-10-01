load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
load "asmTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory asmTheory;
fun print_eval label q =
  let val th = EVAL q in print (label ^ "=" ^ term_to_string (rconc th) ^ "\n") end;
val _ = print_eval "LineLenLabel" ``line_len (labLang$Label 1 0 7:8 labLang$line) = 7``;
val _ = print_eval "LineLenAsmEmpty" ``line_len (labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [] 9:8 labLang$line) = 9``;
val _ = print_eval "LineLenAsmBytesMismatch" ``line_len (labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w;2w;3w] 0:8 labLang$line) = 0``;
val _ = print_eval "LineLenLabAsm" ``line_len (labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:8 word) [4w] 19:8 labLang$line) = 19``;
val _ = print_eval "LineLenWide" ``line_len (labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (3w:64 word) [] 6:64 labLang$line) = 6``;
