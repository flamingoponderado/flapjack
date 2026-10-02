import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Compiler.Backend.LabToTarget.LabsDomain
import Flapjack.Compiler.Backend.LabProps.LabelSets
import Flapjack.Compiler.Backend.BackendProps
import Flapjack.Misc.Sptree.ToAList
import Mathlib.Data.Set.Insert
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.BackendProps

/-- Flapjack set-membership infrastructure; no independently named HOL original. -/
private theorem memImageZero (labels : Set (Nat × Nat)) (k : Nat) :
    k ∈ Prod.fst '' restrictZero labels ↔ (k,0) ∈ labels := by
  constructor
  · rintro ⟨⟨a,b⟩, ⟨h,hzero⟩, rfl⟩
    simpa using hzero ▸ h
  · intro h
    exact ⟨(k,0), ⟨h,rfl⟩, rfl⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "zero_labs_acc_of_eq_zero_labs_of"
  (words_as_type_indexed_bitvec)]
theorem zeroLabsAccOf_eq_zeroLabsOf {width : Nat} [NeZero width]
    (l : AsmWithLab HolCmp (HolRegImm width) MlString) (acc : NumSet) :
    sptDomain (zeroLabsAccOf l acc) = Prod.fst '' restrictZero (labsOf l) ∪ sptDomain acc := by
  ext k
  change sptDomain (zeroLabsAccOf l acc) k ↔
    k ∈ Prod.fst '' restrictZero (labsOf l) ∨ sptDomain acc k
  rw [memImageZero]
  cases l with
  | jump target | jumpCmp _ _ _ target | locValue _ target =>
      cases target with
      | lab a b =>
        by_cases hb : b = 0
        · subst b
          simp [zeroLabsAccOf, labsOf, sptDomainInsert]
        · simp [zeroLabsAccOf, labsOf, hb, eq_comm]
  | call _ | callFFI _ | install | halt => simp [zeroLabsAccOf, labsOf]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_get_zero_labs_acc_eq_line_get_zero_labels"
  (words_as_type_indexed_bitvec)]
theorem lineGetZeroLabsAcc_eq_lineGetZeroLabels {width : Nat} [NeZero width]
    (l : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (acc : NumSet) :
    sptDomain (lineGetZeroLabsAcc l acc) = Prod.fst '' restrictZero (lineGetLabels l) ∪ sptDomain acc := by
  cases l with
  | labAsm instruction _ _ _ => exact zeroLabsAccOf_eq_zeroLabsOf instruction acc
  | label _ _ _ | asm _ _ _ =>
    ext k
    change sptDomain acc k ↔ k ∈ Prod.fst '' restrictZero ∅ ∨ sptDomain acc k
    rw [memImageZero]
    simp

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_get_zero_labs_acc_eq_sec_get_zero_labels"
  (words_as_type_indexed_bitvec)]
theorem secGetZeroLabsAcc_eq_secGetZeroLabels {width : Nat} [NeZero width]
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (acc : NumSet) :
    sptDomain (secGetZeroLabsAcc sec acc) = Prod.fst '' restrictZero (secGetLabels sec) ∪ sptDomain acc := by
  rcases sec with ⟨id,lines⟩
  induction lines with
  | nil => ext k
           change sptDomain acc k ↔ k ∈ Prod.fst '' restrictZero (secGetLabels ⟨id,[]⟩) ∨ sptDomain acc k
           rw [memImageZero]
           simp [secGetLabels]
  | cons line lines ih =>
    change sptDomain (lineGetZeroLabsAcc line (secGetZeroLabsAcc ⟨id,lines⟩ acc)) = _
    rw [lineGetZeroLabsAcc_eq_lineGetZeroLabels, ih]
    ext k
    change (k ∈ Prod.fst '' restrictZero (lineGetLabels line) ∨
      k ∈ Prod.fst '' restrictZero (secGetLabels ⟨id,lines⟩) ∨ sptDomain acc k) ↔
      k ∈ Prod.fst '' restrictZero (secGetLabels ⟨id,line::lines⟩) ∨ sptDomain acc k
    simp only [memImageZero]
    simp [secGetLabels, or_assoc]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_zero_labs_acc_eq_get_zero_labels"
  (words_as_type_indexed_bitvec)]
theorem getZeroLabsAcc_eq_getZeroLabels {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (acc : NumSet) :
    sptDomain (code.foldr secGetZeroLabsAcc acc) = Prod.fst '' restrictZero (getLabels code) ∪ sptDomain acc := by
  induction code with
  | nil => ext k
           change sptDomain acc k ↔ k ∈ Prod.fst '' restrictZero (getLabels ([] : List _)) ∨ sptDomain acc k
           rw [memImageZero]
           simp [getLabels]
  | cons sec code ih =>
    change sptDomain (secGetZeroLabsAcc sec (code.foldr secGetZeroLabsAcc acc)) = _
    rw [secGetZeroLabsAcc_eq_secGetZeroLabels, ih]
    ext k
    change (k ∈ Prod.fst '' restrictZero (secGetLabels sec) ∨
      k ∈ Prod.fst '' restrictZero (getLabels code) ∨ sptDomain acc k) ↔
      k ∈ Prod.fst '' restrictZero (getLabels (sec::code)) ∨ sptDomain acc k
    simp only [memImageZero]
    simp [getLabels_cons, or_assoc]


/-- Flapjack lookup infrastructure, not an independently named HOL declaration. -/
private theorem zeroLookupTest {α : Type} (labs : Spt (Spt α)) (k : Nat) :
    (match sptLookup k labs with
      | none => false
      | some inner => (sptLookup 0 inner).isSome) = true ↔ (k,0) ∈ labsDomain labs := by
  cases h : sptLookup k labs with
  | none => simp [labsDomain, labLookup, h]
  | some inner =>
      cases hi : sptLookup 0 inner <;> simp [labsDomain, labLookup, h, hi]

/-- Full original equivalence. The map-value carrier α remains independent of
code's positive word dimension; the source does not specialize it to Nat. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "zero_labs_acc_exist_eq"
  (words_as_type_indexed_bitvec)]
theorem zeroLabsAccExist_eq {width : Nat} [NeZero width] {α : Type}
    (labs : Spt (Spt α)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    zeroLabsAccExist labs code = true ↔ restrictZero (getLabels code) ⊆ labsDomain labs := by
  have hd (k : Nat) : sptDomain (getZeroLabsAcc code) k ↔ (k,0) ∈ getLabels code := by
    unfold getZeroLabsAcc
    rw [getZeroLabsAcc_eq_getZeroLabels]
    change (k ∈ Prod.fst '' restrictZero (getLabels code) ∨ sptDomain (.ln : NumSet) k) ↔ _
    rw [memImageZero]
    simp [sptDomain, sptLookup]
  unfold zeroLabsAccExist
  rw [List.all_eq_true]
  constructor
  · intro h pair hp
    rcases pair with ⟨k,n⟩
    rcases hp with ⟨hp,hzero⟩
    change n = 0 at hzero
    subst n
    have hk := (hd k).mpr hp
    cases hl : sptLookup k (getZeroLabsAcc code) with
    | none => simp [sptDomain, hl] at hk
    | some value =>
      cases value
      exact (zeroLookupTest labs k).mp (h (k,()) ((sptMemToAList _ k ()).mpr hl))
  · intro h p hp
    have hl := (sptMemToAList _ p.1 p.2).mp hp
    have hk : sptDomain (getZeroLabsAcc code) p.1 := by simp [sptDomain, hl]
    exact (zeroLookupTest labs p.1).mpr (h ⟨(hd p.1).mp hk,rfl⟩)

end Flapjack.Compiler.Backend.LabToTarget
