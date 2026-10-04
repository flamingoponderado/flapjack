import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabToTarget.Padding

/-! Original padding similarity chain, preserving arbitrary source accumulators. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
private abbrev NativeLine (width : Nat) [NeZero width] :=
  Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)

/-- Proof infrastructure with no separate HOL original: erase precisely the
bytes, lengths and resolved positions that line_similar ignores. -/
private def normalLine {width : Nat} [NeZero width] (line : NativeLine width) : NativeLine width :=
  match line with
  | .label s l _ => .label s l 0
  | .asm a _ _ => .asm a [] 0
  | .labAsm a _ _ _ => .labAsm a 0 [] 0

private theorem lineSimilar_normal_iff {width : Nat} [NeZero width]
    (a b : NativeLine width) : lineSimilar a b ↔ normalLine a = normalLine b := by
  cases a <;> cases b <;> simp [lineSimilar, normalLine]

/-- List relation infrastructure for the original EVERY2; no separate HOL
source declaration is claimed for the normalized-map characterization. -/
private theorem linesRel_normal_iff {width : Nat} [NeZero width]
    (a b : List (NativeLine width)) :
    LinesRel lineSimilar a b ↔ a.map normalLine = b.map normalLine := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨fun _ => rfl, fun _ => .nil⟩
    | cons y ys => constructor <;> intro h <;> cases h
  | cons x xs ih =>
    cases b with
    | nil => constructor <;> intro h <;> cases h
    | cons y ys =>
      constructor
      · intro h
        cases h with
        | cons hxy hrest =>
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨(lineSimilar_normal_iff x y).mp hxy, (ih ys).mp hrest⟩
      · intro h
        simp only [List.map_cons, List.cons.injEq] at h
        exact .cons ((lineSimilar_normal_iff x y).mpr h.1) ((ih ys).mpr h.2)

private theorem normal_addNop {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (lines : List (NativeLine width)) :
    (addNop nop lines).map normalLine = lines.map normalLine := by
  induction lines with
  | nil => rfl
  | cons line lines ih =>
    cases line <;> simp [addNop, normalLine, ih]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineSimilar_addNop {width : Nat} [NeZero width]
    (ls ls' : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (h : List (BitVec 8)) :
    LinesRel lineSimilar ls ls' → LinesRel lineSimilar ls (addNop h ls') := by
  intro rel
  apply (linesRel_normal_iff _ _).mpr
  rw [normal_addNop]
  exact (linesRel_normal_iff _ _).mp rel

private theorem normal_padSection {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (lines aux : List (NativeLine width)) :
    (padSection nop lines aux).map normalLine =
      (aux.reverse ++ lines).map normalLine := by
  induction lines generalizing aux with
  | nil => simp [padSection]
  | cons line lines ih =>
    cases line <;>
      simp [padSection, ih, List.map_append, List.map_reverse,
        normalLine, List.append_assoc]
    split <;> simp only [normal_addNop]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineSimilar_padSection {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (l2 aux l1 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar l1 (aux.reverse ++ l2) →
      LinesRel lineSimilar l1 (padSection nop l2 aux) := by
  intro rel
  apply (linesRel_normal_iff _ _).mpr
  rw [normal_padSection]
  exact (linesRel_normal_iff _ _).mp rel

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem codeSimilar_padCode {width : Nat} [NeZero width]
    (code1 code2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (nop : List (BitVec 8)) :
    codeSimilar code1 code2 → codeSimilar code1 (padCode nop code2) := by
  induction code1 generalizing code2 with
  | nil =>
    cases code2 <;> simp [codeSimilar, padCode]
  | cons s rest ih =>
    cases code2 with
    | nil => simp [codeSimilar]
    | cons t tail =>
      cases s with
      | mk n ls =>
        cases t with
        | mk m rs =>
          intro rel
          exact ⟨ih tail rel.1, lineSimilar_padSection nop rs [] ls rel.2.1, rel.2.2⟩

end Flapjack.Compiler.Backend.LabToTarget
