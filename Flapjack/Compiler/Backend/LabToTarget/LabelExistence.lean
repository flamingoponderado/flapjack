import Flapjack.Compiler.Backend.LabToTarget.LabelLookup
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelUpdates
import Flapjack.Compiler.Backend.LabProps.LabelSets
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets

/-- Original lookup-existence predicate retains an arbitrary map value carrier
independent of the positive native word dimension. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def lineLabsExist {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  match line with
  | .labAsm a _ _ _ => ∀ n1 n2, (n1,n2) ∈ labsOf a → labLookup n1 n2 labs ≠ none
  | _ => True

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secLabsExist {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ line ∈ sec.lines, lineLabsExist labs line

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def allLabsExist {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Prop :=
  ∀ sec ∈ code, secLabsExist labs sec

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineSimilar_lineLabsExist {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (l1 l2 : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineSimilar l1 l2 → (lineLabsExist labs l1 ↔ lineLabsExist labs l2) := by
  cases l1 <;> cases l2 <;> simp only [lineSimilar] <;> intro h <;> try contradiction
  all_goals simp [lineLabsExist,h]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem codeSimilar_allLabsExist {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar c1 c2 → (allLabsExist labs c1 ↔ allLabsExist labs c2) := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [codeSimilar,allLabsExist]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      have hs : secLabsExist labs sec ↔ secLabsExist labs sec' := by
        unfold secLabsExist
        have lift : ∀ {xs ys : List (LabLineHOL width)}, LinesRel lineSimilar xs ys →
            ((∀ l ∈ xs,lineLabsExist labs l) ↔ (∀ l ∈ ys,lineLabsExist labs l)) := by
          intro xs ys hr
          induction hr with
          | nil => simp
          | @cons x y xs ys hxy ht iht =>
            simp only [List.mem_cons,forall_eq_or_imp]
            exact and_congr (lineSimilar_lineLabsExist labs x y hxy) iht
        exact lift h.2.1
      simpa [allLabsExist] using and_congr hs (ih rest' h.1)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allLabsExist_padCode {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (nop : List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allLabsExist labs (padCode nop code) ↔ allLabsExist labs code :=
  (codeSimilar_allLabsExist labs code (padCode nop code)
    (codeSimilar_padCode code code nop (codeSimilar_refl code))).symm

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allLabsExist_updLabLen {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allLabsExist labs (updLabLen pos code) ↔ allLabsExist labs code :=
  codeSimilar_allLabsExist labs (updLabLen pos code) code
    ((codeSimilar_updLabLen code pos code).mpr (codeSimilar_refl code))
end Flapjack.Compiler.Backend.LabToTarget
