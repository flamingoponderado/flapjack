import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabToTarget.SecondPass
import Flapjack.FfiHOL
import Flapjack.Misc.Sptree

/-! Full original initial/repeated encoding similarity chain. All accumulator,
position and flag binders are retained; no target relation is assumed. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString Flapjack Flapjack.Misc
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


private theorem normal_encLine {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (len : Nat) (line : NativeLine width) :
    normalLine (encLine enc len line) = normalLine line := by
  cases line <;> rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesRel_encLine {width : Nat} [NeZero width]
    (ls ls' : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (enc : HolAsm width → List (BitVec 8)) (len : Nat) :
    LinesRel lineSimilar ls ls' ↔
      LinesRel lineSimilar (ls.map (encLine enc len)) ls' := by
  rw [linesRel_normal_iff, linesRel_normal_iff]
  simp only [List.map_map]
  have h : normalLine ∘ encLine enc len = normalLine := by
    funext line
    exact normal_encLine enc len line
  rw [h]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem codeSimilar_encSecList {width : Nat} [NeZero width]
    (code1 code2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (n : HolAsm width → List (BitVec 8)) :
    codeSimilar (encSecList n code1) code2 ↔ codeSimilar code1 code2 := by
  induction code1 generalizing code2 with
  | nil => cases code2 <;> simp [encSecList, codeSimilar]
  | cons sec rest ih =>
    cases code2 with
    | nil => simp [encSecList, codeSimilar]
    | cons sec' rest' =>
      cases sec
      cases sec'
      simp only [encSecList, List.map_cons, encSec, codeSimilar]
      rw [← encSecList, ih, ← linesRel_encLine]

/-- Actual recursive encoding invariant used inside the original accumulator
proof; normalization is Flapjack proof infrastructure with no separate HOL tag. -/
private theorem normal_encLinesAgain {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (enc : HolAsm width → List (BitVec 8))
    (lines : List (NativeLine width)) (pos : Nat) (acc : List (NativeLine width))
    (ok : Bool) :
    (encLinesAgain labs ffis pos enc lines acc ok).1.map normalLine =
      (acc.reverse ++ lines).map normalLine := by
  induction lines generalizing pos acc ok with
  | nil => simp [encLinesAgain]
  | cons line lines ih =>
    cases line <;>
      simp [encLinesAgain, ih, List.map_append, List.map_reverse,
        normalLine, List.append_assoc]
    split <;> simp [ih, List.map_append, List.map_reverse, normalLine, List.append_assoc]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encLinesAgain_implies_similar {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool)
    (lines' : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok' : Nat × Bool)
    (curr : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    encLinesAgain labs ffis pos enc lines acc ok = (lines', ok') →
    LinesRel lineSimilar curr acc.reverse →
      LinesRel lineSimilar (curr ++ lines) lines' := by
  intro heq hcurr
  apply (linesRel_normal_iff _ _).mpr
  have h := normal_encLinesAgain labs ffis enc lines pos acc ok
  rw [heq] at h
  simp only [List.map_append] at h ⊢
  rw [(linesRel_normal_iff _ _).mp hcurr]
  exact h.symm

private theorem encSecsAgain_similar {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (enc : HolAsm width → List (BitVec 8))
    (code : List (Section (NativeLine width))) (pos : Nat) :
    codeSimilar code (encSecsAgain pos labs ffis enc code).1 := by
  induction code generalizing pos with
  | nil => trivial
  | cons sec rest ih =>
    cases sec with
    | mk n lines =>
      generalize heq : encLinesAgain labs ffis pos enc lines [] true = result
      rcases result with ⟨lines', pos', ok'⟩
      simp only [encSecsAgain, heq]
      have hlines : LinesRel lineSimilar lines lines' := by
        exact encLinesAgain_implies_similar labs ffis pos enc lines [] true lines'
          (pos',ok') [] heq .nil
      exact ⟨ih pos', hlines, rfl⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecsAgain_implies_similar {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (code code1 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc code = (code1, ok) → codeSimilar code code1 := by
  intro heq
  have h := encSecsAgain_similar labs ffis enc code pos
  rw [heq] at h
  exact h

end Flapjack.Compiler.Backend.LabToTarget
