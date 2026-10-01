(* Direct HOL-EVAL observations for the lab_to_target second-pass definitions
   (lab_to_targetScript.sml:120-166): enc_lines_again, enc_secs_again,
   lines_upd_lab_len and upd_lab_len.  Bead flapjack-pxn.18.5.15.10.13.

   All inputs are concrete 64-bit labLang$line/labLang$sec values.  The section
   map labs is section 7 to {0 -> 10, 3 -> 13}, so find_pos (Lab 7 0) is 10: at
   pos = 10 a Jump (Lab 7 0) has jump offset 0w, which lets w = w1 hold exactly.
   The supplied encoder maps every asm to the three bytes [1w;2w;3w], so the
   re-encoded length 3 is observable in the LabAsm length field and decides
   whether l1 = l keeps the success flag.  ffis is empty (no CallFFI input).

   Rows: the empty line list; a keep-only list with Label/Asm/LabAsm; the same
   LabAsm with a stale word at l = 1 (l1 = 3 > 1, flag F) and at l = 7
   (l1 = max 3 7 = 7, flag T); the empty section list and a two-section list
   whose first re-encodes and second keeps; lines_upd_lab_len empty, at even
   pos (label length 0) and at odd pos (label length 1); and upd_lab_len empty
   and on two sections. *)

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
val ffis = ``[] : ffiname list``;
val enc = ``\(a:64 asm$asm). ([1w;2w;3w] : word8 list)``;

val lineKeep = ``[labLang$LabAsm (labLang$Jump (labLang$Lab 7 0)) (0w:64 word) [] 7;
                  labLang$Label 5 0 4;
                  labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [9w] 2] :
                 64 labLang$line list``;
val lineReencode = ``[labLang$LabAsm (labLang$Jump (labLang$Lab 7 0))
                        (99w:64 word) [] 1] : 64 labLang$line list``;
val lineReencodeLong = ``[labLang$LabAsm (labLang$Jump (labLang$Lab 7 0))
                            (99w:64 word) [] 7] : 64 labLang$line list``;
val secsTwo = ``[labLang$Section 5
                   [labLang$LabAsm (labLang$Jump (labLang$Lab 7 0))
                      (99w:64 word) [] 1];
                  labLang$Section 6
                   [labLang$Label 4 0 2;
                    labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [9w] 5]] :
                 64 labLang$sec list``;
val updLines = ``[labLang$Label 5 0 7;
                  labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [9w] 2;
                  labLang$LabAsm (labLang$Jump (labLang$Lab 7 3))
                    (3w:64 word) [] 4] : 64 labLang$line list``;
val updSecs = ``[labLang$Section 5
                   [labLang$Label 5 0 9;
                    labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [9w] 2];
                  labLang$Section 6
                   [labLang$LabAsm (labLang$Jump (labLang$Lab 7 3))
                      (3w:64 word) [] 3]] : 64 labLang$sec list``;

val _ = print_eval "EncLinesAgainEmpty"
  ``enc_lines_again ^labs ^ffis 10 ^enc
      ([] : 64 labLang$line list) ([],T)``;
val _ = print_eval "EncLinesAgainKeep"
  ``enc_lines_again ^labs ^ffis 10 ^enc ^lineKeep ([],T)``;
val _ = print_eval "EncLinesAgainReencodeShort"
  ``enc_lines_again ^labs ^ffis 10 ^enc ^lineReencode ([],T)``;
val _ = print_eval "EncLinesAgainReencodeLong"
  ``enc_lines_again ^labs ^ffis 10 ^enc ^lineReencodeLong ([],T)``;

val _ = print_eval "EncSecsAgainEmpty"
  ``enc_secs_again 10 ^labs ^ffis ^enc ([] : 64 labLang$sec list)``;
val _ = print_eval "EncSecsAgainTwo"
  ``enc_secs_again 10 ^labs ^ffis ^enc ^secsTwo``;

val _ = print_eval "LinesUpdLabLenEmpty"
  ``lines_upd_lab_len 5 ([] : 64 labLang$line list) []``;
val _ = print_eval "LinesUpdLabLenEven"
  ``lines_upd_lab_len 0 ^updLines []``;
val _ = print_eval "LinesUpdLabLenOdd"
  ``lines_upd_lab_len 1 ^updLines []``;

val _ = print_eval "UpdLabLenEmpty"
  ``upd_lab_len 5 ([] : 64 labLang$sec list)``;
val _ = print_eval "UpdLabLenTwo"
  ``upd_lab_len 0 ^updSecs``;
