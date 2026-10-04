import Flapjack.Compiler.Backend.LabToTarget.LabelLookup
import Flapjack.Compiler.Backend.LabToTarget.NopEncoding
import Flapjack.Compiler.Backend.LabProps.LineLength
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps

/-- Full original instruction/encoding validity, preserving unsupported Call,
failed label lookup and every byte-length/assembler-validity conjunct. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def lineOk {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  match line with
  | .label _ _ l => pos % 2 = 0 ∧ l = 0
  | .asm b bytes l =>
    encWithNop c.encode (cbwToAsmHOL b) bytes ∧
    bytes.length = l ∧ asmOkExact (cbwToAsmHOL b) c = true
  | .labAsm .halt _ bytes l =>
    let w1 : BitVec width := 0 - BitVec.ofNat width (pos + ffiOffset)
    encWithNop c.encode (.jump w1) bytes ∧ bytes.length = l ∧
      asmOkExact (.jump w1) c = true
  | .labAsm .install _ bytes l =>
    let w1 : BitVec width := 0 - BitVec.ofNat width (pos + 2 * ffiOffset)
    encWithNop c.encode (.jump w1) bytes ∧ bytes.length = l ∧
      asmOkExact (.jump w1) c = true
  | .labAsm (.callFFI index) _ bytes l =>
    let w1 : BitVec width := 0 - BitVec.ofNat width
      (pos + (3 + getFfiIndex ffis (.extCall index)) * ffiOffset)
    encWithNop c.encode (.jump w1) bytes ∧ bytes.length = l ∧
      asmOkExact (.jump w1) c = true
  | .labAsm (.call _) _ _ _ => False
  | .labAsm a _ bytes l =>
    match getLabel a with
    | .lab l1 l2 => match labLookup l1 l2 labs with
      | none => False
      | some t =>
        let w1 := BitVec.ofNat width t - BitVec.ofNat width pos
        encWithNop c.encode (labInst w1 a) bytes ∧ bytes.length = l ∧
          asmOkExact (labInst w1 a) c = true

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def linesOk {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  match lines with
  | [] => True
  | y :: ys => lineOk c labs ffis pos y ∧ linesOk c labs ffis (pos + lineLength y) ys

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def allEncOk {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Prop :=
  match code with
  | [] => True
  | ⟨_, []⟩ :: xs => pos % 2 = 0 ∧ allEncOk c labs ffis pos xs
  | ⟨k, y :: ys⟩ :: xs =>
    lineOk c labs ffis pos y ∧ allEncOk c labs ffis (pos + lineLength y) (⟨k, ys⟩ :: xs)
termination_by code.length + (code.map (fun sec => sec.lines.length)).sum
decreasing_by all_goals simp_wf

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_cons {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos k : Nat)
    (xs : List (Section (LabLineHOL width))) :
    allEncOk c labs ffis pos (⟨k, ls⟩ :: xs) ↔
    allEncOk c labs ffis (pos + (ls.map lineLength).sum) xs ∧
      (pos + (ls.map lineLength).sum) % 2 = 0 ∧ linesOk c labs ffis pos ls := by
  induction ls generalizing pos with
  | nil => simp [allEncOk, linesOk, and_comm]
  | cons y ys ih =>
    rw [allEncOk]
    rw [ih]
    simp [linesOk, Nat.add_assoc, and_assoc, and_comm]

/-- Flapjack proof infrastructure: constructor elimination extracts the actual
zero-label conjunct. There is no separately named HOL lemma for this projection. -/
private theorem lineOk_labelZero {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (line : LabLineHOL width) :
    lineOk c labs ffis pos line → labelZero line := by
  cases line with
  | label _ _ _ => exact fun h => h.2
  | asm _ _ _ => exact fun _ => True.intro
  | labAsm _ _ _ _ => exact fun _ => True.intro

/-- Flapjack proof infrastructure: list induction projects the zero-label facts
from linesOk, without weakening its encoding/length/validity/alignment content. -/
private theorem linesOk_labelsZero {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (lines : List (LabLineHOL width)) :
    linesOk c labs ffis pos lines → ∀ line ∈ lines, labelZero line := by
  induction lines generalizing pos with
  | nil => simp
  | cons y ys ih =>
    intro h line hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact lineOk_labelZero c labs ffis pos line h.1
    · exact ih _ h.2 line hm

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_implies_secLabelZero {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (n : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncOk conf labs ffis n code → ∀ sec ∈ code, secLabelZero sec := by
  induction code generalizing n with
  | nil => simp
  | cons sec code ih =>
    rcases sec with ⟨k, lines⟩
    rw [allEncOk_cons]
    intro h sec hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact linesOk_labelsZero conf labs ffis n lines h.2.2
    · exact ih _ h.1 sec hm

/-- Full original zero-position theorem. The source's unused forall enc binder
is vacuous (absent from premise and conclusion) and is omitted after source review. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem posVal_zero {width : Nat} [NeZero width]
    (xs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat) :
    allEncOk c labs ffis pos xs → posVal 0 pos xs = pos := by
  intro h
  exact secLabelZero_posVal_zero xs pos (allEncOk_implies_secLabelZero c labs ffis pos xs h)

/-- Flapjack proof infrastructure: physical-byte upper bound extracted from
zero label annotations over the actual native position/byte recursions. This
intermediate strengthening has no separately named original HOL declaration. -/
private theorem posVal_bound_labelsZero {width : Nat} [NeZero width]
    (code : LabProgHOL width) (i pos : Nat) :
    (∀ sec ∈ code, secLabelZero sec) →
    posVal i pos code ≤ pos + (progToBytes code).length := by
  induction code generalizing i pos with
  | nil => simp [posVal, progToBytes]
  | cons sec code ih =>
    rcases sec with ⟨k, lines⟩
    intro h
    have htail : ∀ sec ∈ code, secLabelZero sec := fun sec hm => h sec (by simp [hm])
    have hlines : ∀ line ∈ lines, labelZero line := h ⟨k, lines⟩ (by simp)
    clear h
    induction lines generalizing i pos with
    | nil => rw [posVal, progToBytes]; exact ih i pos htail
    | cons line lines ihLines =>
      have hhead := hlines line (by simp)
      have ht : ∀ line ∈ lines, labelZero line := fun line hm => hlines line (by simp [hm])
      cases line with
      | label sid lid n =>
        simp only [labelZero] at hhead
        subst n
        rw [posVal, progToBytes]
        simp only [isLabelHOL, ↓reduceIte, lineLength, lineBytes,
          Nat.add_zero, List.nil_append]
        exact ihLines i pos ht
      | asm b bytes l =>
        rw [posVal, progToBytes]
        simp only [isLabelHOL, Bool.false_eq_true, ↓reduceIte, lineLength,
          lineBytes, List.length_append]
        by_cases hi : i = 0
        · simp only [hi, ↓reduceIte]; omega
        · simp only [hi, ↓reduceIte]
          have hb := ihLines (i - 1) (pos + bytes.length) ht
          omega
      | labAsm a w bytes l =>
        rw [posVal, progToBytes]
        simp only [isLabelHOL, Bool.false_eq_true, ↓reduceIte, lineLength,
          lineBytes, List.length_append]
        by_cases hi : i = 0
        · simp only [hi, ↓reduceIte]; omega
        · simp only [hi, ↓reduceIte]
          have hb := ihLines (i - 1) (pos + bytes.length) ht
          omega

/-- Full original position bound. The position being bounded is independent of
n, the starting position at which the code's encoding validity is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem posVal_bound {width : Nat} [NeZero width] (i pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (conf : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffi : List HolFfiName) (n : Nat) :
    allEncOk conf labs ffi n code → posVal i pos code ≤ pos + (progToBytes code).length := by
  intro h
  exact posVal_bound_labelsZero code i pos
    (allEncOk_implies_secLabelZero conf labs ffi n code h)

end Flapjack.Compiler.Backend.LabToTarget
