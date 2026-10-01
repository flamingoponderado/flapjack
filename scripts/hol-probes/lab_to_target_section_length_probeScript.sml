load "bossLib";
load "preamble";
load "lab_to_targetTheory";
load "lab_to_targetProofTheory";
load "asmTheory";
open bossLib HolKernel Parse preamble lab_to_targetTheory lab_to_targetProofTheory asmTheory;
fun print_eval label q =
  let val th = EVAL q in print (label ^ "=" ^ term_to_string (rconc th) ^ "\n") end;
val mixed = ``[labLang$Label 1 0 3; labLang$Label 1 4 2;
  labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w] 4;
  labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:8 word) [2w] 5] : 8 labLang$line list``;
val acc = ``[(99,7)] : (num # num) list``;
val _ = print_eval "SectionLengthEmpty" ``FST(section_labels 5 ([]:8 labLang$line list) ^acc) = sec_length [] 5``;
val _ = print_eval "SectionLengthMixed" ``FST(section_labels 17 ^mixed ^acc) = sec_length ^mixed 17``;
val _ = print_eval "SectionLengthMixedPosition" ``FST(section_labels 17 ^mixed ^acc) = 31``;
val _ = print_eval "SectionLengthMixedLabels" ``section_labels 17 ^mixed ^acc = (31,[(4,22);(99,7)])``;
val _ = print_eval "SectionLengthZeroLabel" ``section_labels 3 [labLang$Label 1 0 7:8 labLang$line] ^acc = (10,^acc)``;
val _ = print_eval "SectionLengthZeroLenLabel" ``section_labels 0 [labLang$Label 1 9 0:8 labLang$line] ^acc = (0,[(9,0);(99,7)])``;
val _ = print_eval "SectionLengthDuplicateLabels" ``section_labels 4 [labLang$Label 1 2 1;labLang$Label 1 2 2:8 labLang$line] ^acc = (7,[(2,7);(2,5);(99,7)])``;
val _ = print_eval "SectionLengthArbitraryAccumulator" ``FST(section_labels 37 ^mixed [(0,900);(4,0);(4,999)]) = sec_length ^mixed 37``;

(* Exact sec_length_add3135, independent of annotation/byte consistency. *)
val _ = print_eval "SecLengthAddEmpty" ``sec_length ([]:8 labLang$line list) (5+7) = sec_length [] 5 + 7``;
val _ = print_eval "SecLengthAddMixed" ``sec_length ^mixed (17+9) = sec_length ^mixed 17 + 9``;
val _ = print_eval "SecLengthAddMixedValue" ``sec_length ^mixed (17+9) = 40``;
val _ = print_eval "SecLengthAddZeroAnnotation" ``sec_length [labLang$Label 1 2 0; labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [] 0:8 labLang$line] (3+4) = 7``;
val _ = print_eval "SecLengthAddEmptyBytesAnnotation" ``sec_length [labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [] 100:8 labLang$line] (2+6) = 108``;
