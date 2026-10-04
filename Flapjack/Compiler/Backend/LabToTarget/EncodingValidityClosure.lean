import Flapjack.Compiler.Backend.LabToTarget.ByteLengths
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Full original append closure at the physical-byte-adjusted second start.
Both input validity guards retain every original encoding/length/label/parity
condition; none of those facts are replaced by output validity assumptions. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_append {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (left right : List (Section
      (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncOk c labs ffis pos left ∧
    allEncOk c labs ffis (pos + (progToBytes left).length) right →
    allEncOk c labs ffis pos (left ++ right) := by
  induction left generalizing pos with
  | nil =>
    rintro ⟨_,hr⟩
    simp only [progToBytes.eq_1,List.length_nil,Nat.add_zero] at hr
    exact hr
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    rintro ⟨hl,hr⟩
    have hh := (allEncOk_cons c labs ffis lines pos sid rest).mp hl
    have hlength : (progToBytes (⟨sid,lines⟩::rest)).length =
        (lines.map lineLength).sum + (progToBytes rest).length := by
      rw [progToBytesMap]
      simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_flatten]
      rw [linesOk_mapLineByteLength lines c labs ffis pos hh.2.2]
      rw [progToBytesMap]
      simp only [List.length_flatten]
    apply (allEncOk_cons c labs ffis lines pos sid (rest ++ right)).mpr
    refine ⟨ih (pos + (lines.map lineLength).sum) ⟨hh.1,?_⟩,hh.2⟩
    simpa only [hlength,Nat.add_assoc] using hr

/-- Flapjack constructor infrastructure for the actual original lookup-extension
hypothesis. It has no independently named HOL declaration and assumes no target
encoding fact. -/
private theorem lineOk_extend {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs extended : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : LabLineHOL width)
    (hm : ∀ sid lid value,labLookup sid lid labs = some value →
      labLookup sid lid extended = some value)
    (h : lineOk c labs ffis pos line) : lineOk c extended ffis pos line := by
  cases line with
  | label _ _ _ => exact h
  | asm _ _ _ => exact h
  | labAsm a w bytes len =>
    cases a with
    | halt => exact h
    | install => exact h
    | callFFI name => exact h
    | call label => exact h
    | jump label =>
      cases label with
      | lab sid lid =>
        cases hl : labLookup sid lid labs with
        | none => simp [lineOk,getLabel,hl] at h
        | some value => simpa [lineOk,getLabel,hl,hm sid lid value hl] using h
    | jumpCmp cmp reg imm label =>
      cases label with
      | lab sid lid =>
        cases hl : labLookup sid lid labs with
        | none => simp [lineOk,getLabel,hl] at h
        | some value => simpa [lineOk,getLabel,hl,hm sid lid value hl] using h
    | locValue reg label =>
      cases label with
      | lab sid lid =>
        cases hl : labLookup sid lid labs with
        | none => simp [lineOk,getLabel,hl] at h
        | some value => simpa [lineOk,getLabel,hl,hm sid lid value hl] using h

/-- Full original map-extension closure: every successful old lookup must be
preserved, and complete original input validity establishes complete validity
under the extended canonical label map. No side condition on failed lookups or
map domains is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_extendLabels {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (code : List (Section
      (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (extended : Spt (Spt Nat)) :
    (∀ sid lid value,labLookup sid lid labs = some value →
      labLookup sid lid extended = some value) ∧ allEncOk c labs ffis pos code →
    allEncOk c extended ffis pos code := by
  rintro ⟨hm,h⟩
  induction code generalizing pos with
  | nil => simp [allEncOk]
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    have hh := (allEncOk_cons c labs ffis lines pos sid rest).mp h
    apply (allEncOk_cons c extended ffis lines pos sid rest).mpr
    refine ⟨ih _ hh.1,hh.2.1,?_⟩
    have hl := hh.2.2
    clear h hh
    induction lines generalizing pos with
    | nil => trivial
    | cons line lines ihLines =>
      exact ⟨lineOk_extend c labs extended ffis pos line hm hl.1,ihLines _ hl.2⟩
end Flapjack.Compiler.Backend.LabToTarget
