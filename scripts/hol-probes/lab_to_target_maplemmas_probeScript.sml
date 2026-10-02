(* Direct HOL-EVAL observations for the two lab_to_target MAP lemmas
   (lab_to_targetScript.sml):
     - pad_code_MAP  (line 226):
         pad_code nop =
           MAP (\\x. Section (Section_num x) (pad_section nop (Section_lines x) []))
     - prog_to_bytes_MAP (line 341):
         !ls. prog_to_bytes ls =
              FLAT (MAP (FLAT o MAP line_bytes o Section_lines) ls)
   Bead flapjack-pxn.18.5.15.10.29.

   Every row evaluates the original HOL definitions directly.  The *Eq rows
   compare the two sides of the theorem on a concrete input (EVAL reduces the
   comparison to T), and the *Lhs/*Rhs rows print each side's observed value so
   the equality and the concrete result are both captured.  All line/section
   inputs are concrete 64-bit labLang$line/labLang$sec values. *)

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

(* pad_code_MAP: concrete two-section input, one padded section and one empty. *)
val secOne = ``labLang$Section 1
   [labLang$Label 1 2 0;
    labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w;2w] 3] : 64 labLang$sec``;
val secTwo = ``labLang$Section 2 ([] : 64 labLang$line list) : 64 labLang$sec``;
val secList = ``[^secOne; ^secTwo] : 64 labLang$sec list``;
val padMapF =
  ``\(x:64 labLang$sec).
      Section (Section_num x) (pad_section [9w] (Section_lines x) [])``;

val _ = print_eval "PadCodeMapEmptyEq"
  ``pad_code [9w] ([] : 64 labLang$sec list) =
      MAP ^padMapF ([] : 64 labLang$sec list)``;
val _ = print_eval "PadCodeMapConcreteEq"
  ``pad_code [9w] ^secList = MAP ^padMapF ^secList``;
val _ = print_eval "PadCodeMapConcreteLhs" ``pad_code [9w] ^secList``;
val _ = print_eval "PadCodeMapConcreteRhs" ``MAP ^padMapF ^secList``;

(* prog_to_bytes_MAP: the section list from the sibling removelabels probe,
   including an empty section that prog_to_bytes skips. *)
val bytesCode = ``[labLang$Section 1
    [labLang$Label 1 2 3;
     labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [1w;2w] 2];
   labLang$Section 2 ([] : 64 labLang$line list);
   labLang$Section 3
    [labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:64 word) [3w] 1]]
   : 64 labLang$sec list``;
val p2bMap =
  ``\(ls:64 labLang$sec list).
      FLAT (MAP (FLAT o MAP line_bytes o Section_lines) ls)``;

val _ = print_eval "ProgToBytesMapEmptyEq"
  ``prog_to_bytes ([] : 64 labLang$sec list) =
      FLAT (MAP (FLAT o MAP line_bytes o Section_lines)
        ([] : 64 labLang$sec list))``;
val _ = print_eval "ProgToBytesMapConcreteEq"
  ``prog_to_bytes ^bytesCode = ^p2bMap ^bytesCode``;
val _ = print_eval "ProgToBytesMapConcreteLhs" ``prog_to_bytes ^bytesCode``;
val _ = print_eval "ProgToBytesMapConcreteRhs" ``^p2bMap ^bytesCode``;
