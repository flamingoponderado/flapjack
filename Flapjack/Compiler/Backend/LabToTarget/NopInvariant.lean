import Flapjack.Compiler.Backend.LabToTarget.PositionalEncoding
import Flapjack.Compiler.Backend.LabToTarget.NopEncoding
import Flapjack.Compiler.Backend.LabToTarget.LengthCorrectness
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- The original Call clause checks only byte length; it imposes no encoding relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def lineEncWithNop {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  match line with
  | .asm b bytes len => encWithNop enc (cbwToAsmExact b) bytes ∧ bytes.length = len
  | .labAsm .halt _ bytes len =>
      encWithNop enc (.jump (-BitVec.ofNat width (pos + ffiOffset))) bytes ∧ bytes.length = len
  | .labAsm .install _ bytes len =>
      encWithNop enc (.jump (-BitVec.ofNat width (pos + 2 * ffiOffset))) bytes ∧ bytes.length = len
  | .labAsm (.callFFI name) _ bytes len =>
      encWithNop enc (.jump (-BitVec.ofNat width (pos + (getFfiIndex ffis (.extCall name) + 3) * ffiOffset))) bytes ∧
        bytes.length = len
  | .labAsm (.jump label) _ bytes len =>
      encWithNop enc (.jump (BitVec.ofNat width (findPos label labs) + -BitVec.ofNat width pos)) bytes ∧
        bytes.length = len
  | .labAsm (.jumpCmp cmp reg imm label) _ bytes len =>
      encWithNop enc (.jumpCmp cmp reg imm (BitVec.ofNat width (findPos label labs) + -BitVec.ofNat width pos)) bytes ∧
        bytes.length = len
  | .labAsm (.locValue reg label) _ bytes len =>
      encWithNop enc (.loc reg (BitVec.ofNat width (findPos label labs) + -BitVec.ofNat width pos)) bytes ∧
        bytes.length = len
  | .labAsm (.call _) _ bytes len => bytes.length = len
  | .label _ _ len => len = 0

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def linesEncWithNop {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Prop
  | [] => True
  | line :: rest => lineEncWithNop enc labs ffis pos line ∧
      linesEncWithNop enc labs ffis (pos + lineLength line) rest

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesEncWithNop_append {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesEncWithNop enc labs ffis pos (l1 ++ l2) ↔
      linesEncWithNop enc labs ffis pos l1 ∧
      linesEncWithNop enc labs ffis (pos + (l1.map lineLength).sum) l2 := by
  induction l1 generalizing pos with
  | nil => simp [linesEncWithNop]
  | cons line rest ih =>
    simp [linesEncWithNop, ih, Nat.add_assoc, and_assoc]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def allEncWithNop {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → Prop
  | [] => True
  | ⟨_, []⟩ :: rest => allEncWithNop enc labs ffis pos rest
  | ⟨id, line :: tail⟩ :: rest => lineEncWithNop enc labs ffis pos line ∧
      allEncWithNop enc labs ffis (pos + lineLength line) (⟨id, tail⟩ :: rest)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncWithNop_alt {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (id : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (allEncWithNop enc labs ffis pos [] ↔ True) ∧
      (allEncWithNop enc labs ffis pos (⟨id, ls⟩ :: ss) ↔
        linesEncWithNop enc labs ffis pos ls ∧
        allEncWithNop enc labs ffis (pos + (ls.map lineLength).sum) ss) := by
  constructor
  · simp [allEncWithNop]
  · induction ls generalizing pos with
    | nil => simp [allEncWithNop, linesEncWithNop]
    | cons line rest ih =>
      simp [allEncWithNop, linesEncWithNop, ih, Nat.add_assoc, and_assoc]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineEncWithNop_lengthOk {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineEncWithNop enc labs ffis pos line → lineLengthOk line := by
  cases line with
  | label => simp [lineEncWithNop, lineLengthOk, lineBytes, lineLen]; omega
  | asm => simp [lineEncWithNop, lineLengthOk, lineBytes, lineLen]
  | labAsm a => cases a <;> simp [lineEncWithNop, lineLengthOk, lineBytes, lineLen]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesEncWithNop_lengthOk {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesEncWithNop enc labs ffis pos ls → ∀ line ∈ ls, lineLengthOk line := by
  induction ls generalizing pos with
  | nil => simp
  | cons line rest ih =>
    rintro ⟨hl, hr⟩
    simpa using And.intro (lineEncWithNop_lengthOk enc labs ffis pos line hl) (ih _ hr)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineEncWithNop_labelZero {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineEncWithNop enc labs ffis pos line → labelZero line := by
  cases line with
  | label => simp [lineEncWithNop, labelZero]
  | asm => simp [lineEncWithNop, labelZero]
  | labAsm a => cases a <;> simp [lineEncWithNop, labelZero]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesEncWithNop_labelZero {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesEncWithNop enc labs ffis pos ls → ∀ line ∈ ls, labelZero line := by
  induction ls generalizing pos with
  | nil => simp
  | cons line rest ih =>
    rintro ⟨hl, hr⟩
    simpa using And.intro (lineEncWithNop_labelZero enc labs ffis pos line hl) (ih _ hr)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncWithNop_labelZero {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncWithNop enc labs ffis pos ss → ∀ sec ∈ ss, secLabelZero sec := by
  induction ss generalizing pos with
  | nil => simp
  | cons sec rest ih =>
    rcases sec with ⟨id, ls⟩
    intro h
    have hh := (allEncWithNop_alt enc labs ffis pos id ls rest).2.mp h
    have hf : secLabelZero ⟨id, ls⟩ := linesEncWithNop_labelZero enc labs ffis pos ls hh.1
    simpa using And.intro hf (ih _ hh.2)

end Flapjack.Compiler.Backend.LabToTarget
