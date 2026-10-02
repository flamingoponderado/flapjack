import Flapjack.Compiler.Encoders.Asm
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.LabToTarget.SectionLength
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Original parity clause: even-position labels record zero, odd labels one;
Asm and LabAsm are unconstrained. HOL EVEN is ordinary Nat modulo two. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_lab_len_pos_ok_def"
  (words_as_type_indexed_bitvec)]
def lineLabLenPosOk {width : Nat} [NeZero width] (pos : Nat) :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Prop
  | .label _ _ len => if pos % 2 = 0 then len = 0 else len = 1
  | .asm _ _ _ => True
  | .labAsm _ _ _ _ => True

/-- Positions advance through the original annotations, not physical bytes. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_len_pos_ok_def"
  (words_as_type_indexed_bitvec)]
def labLenPosOk {width : Nat} [NeZero width] (pos : Nat) :
    List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Prop
  | [] => True
  | line :: rest => lineLabLenPosOk pos line ∧ labLenPosOk (pos + lineLen line) rest

/-- Full original arbitrary append equivalence with annotated position advancement. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_len_pos_ok_append"
  (words_as_type_indexed_bitvec)]
theorem labLenPosOk_append {width : Nat} [NeZero width]
    (l1 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat)
    (l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labLenPosOk pos (l1 ++ l2) ↔ labLenPosOk pos l1 ∧ labLenPosOk (pos + (l1.map lineLen).sum) l2 := by
  induction l1 generalizing pos with
  | nil => simp [labLenPosOk]
  | cons line rest ih => simp [labLenPosOk,ih,Nat.add_assoc,and_assoc]

/-- Retains the source section traversal and actual secLength annotation sum. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_lab_len_pos_ok_def"
  (words_as_type_indexed_bitvec)]
def allLabLenPosOk {width : Nat} [NeZero width] (pos : Nat) :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → Prop
  | [] => True
  | sec :: rest => labLenPosOk pos sec.lines ∧ allLabLenPosOk (pos + secLength sec.lines 0) rest
end Flapjack.Compiler.Backend.LabToTarget
