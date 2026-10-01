(* Direct HOL-EVAL observations for the lab_to_target label-computation
   definitions (lab_to_targetScript.sml:62-83): section_labels and
   compute_labels_alt.

   The probe supplies concrete 8-bit labLang line/sec values and a count of
   the two-level num_map that compute_labels_alt builds: section id ->
   (label number -> byte offset).  section_labels 10 lines [] starts at
   position 10 and advances by each line's length; the zero label is ignored
   and the nonzero labels 1 and 2 are recorded at 13 and 17.  compute_labels_alt
   over two sections then seeds each inner map with its section start under
   key 0 (10 for section 1, 13 for section 2) and records labels 1 and 2 at 13
   and 20. *)

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

val label0 = ``(labLang$Label 0 0 0 : 8 labLang$line)``;
val asm1 = ``(labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [] 1 : 8 labLang$line)``;
val label1 = ``(labLang$Label 0 1 2 : 8 labLang$line)``;
val label2 = ``(labLang$Label 0 2 4 : 8 labLang$line)``;
val asm2 = ``(labLang$Asm (labLang$Cbw 1 2) [] 2 : 8 labLang$line)``;
val labasm3 = ``(labLang$LabAsm (labLang$Halt : 8 labLang$asm_with_lab) 0w [] 3 :
  8 labLang$line)``;
val lines = ``[^label0; ^asm1; ^label1; ^label2; ^asm2; ^labasm3]``;

val sec1 = ``(labLang$Section 1 [^label0; ^asm1; ^label1] : 8 labLang$sec)``;
val sec2 = ``(labLang$Section 2 [^labasm3; ^label2] : 8 labLang$sec)``;

val _ = print_eval "SectionLabelsEmpty" ``section_labels 5 [] []``;
val _ = print_eval "SectionLabelsEmptyLabs" ``section_labels 5 [] [(9,9)]``;
val _ = print_eval "SectionLabelsConcrete" ``section_labels 10 ^lines []``;
val _ = print_eval "SectionLabelsConcreteLabs" ``section_labels 10 ^lines [(7,7)]``;
val _ = print_eval "ComputeLabelsAltEmpty" ``compute_labels_alt 5 [] LN``;
val _ = print_eval "ComputeLabelsAltConcrete"
  ``compute_labels_alt 10 [^sec1; ^sec2] LN``;
val _ = print_eval "ComputeLookupSection1"
  ``lookup 1 (compute_labels_alt 10 [^sec1; ^sec2] LN)``;
val _ = print_eval "ComputeLookupSection2"
  ``lookup 2 (compute_labels_alt 10 [^sec1; ^sec2] LN)``;
val _ = print_eval "ComputeLookupSection3Absent"
  ``lookup 3 (compute_labels_alt 10 [^sec1; ^sec2] LN)``;
val _ = print_eval "ComputeLookupSection1Start"
  ``case lookup 1 (compute_labels_alt 10 [^sec1; ^sec2] LN) of
      NONE => NONE
    | SOME m => lookup 0 m``;
val _ = print_eval "ComputeLookupSection1Label1"
  ``case lookup 1 (compute_labels_alt 10 [^sec1; ^sec2] LN) of
      NONE => NONE
    | SOME m => lookup 1 m``;
val _ = print_eval "ComputeLookupSection2Start"
  ``case lookup 2 (compute_labels_alt 10 [^sec1; ^sec2] LN) of
      NONE => NONE
    | SOME m => lookup 0 m``;
val _ = print_eval "ComputeLookupSection2Label2"
  ``case lookup 2 (compute_labels_alt 10 [^sec1; ^sec2] LN) of
      NONE => NONE
    | SOME m => lookup 2 m``;
