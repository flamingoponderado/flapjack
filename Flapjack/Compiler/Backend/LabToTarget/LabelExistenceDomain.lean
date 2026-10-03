import Flapjack.Compiler.Backend.LabToTarget.LabelExistence
import Flapjack.Compiler.Backend.LabToTarget.LabsDomain
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets

/-- Full original unconditional label-existence/domain equivalence, retaining
an arbitrary independent map value carrier and the native positive word carrier. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "line_labs_exist_get_labels" (words_as_type_indexed_bitvec)]
theorem lineLabsExist_iff_labelsSubset {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineLabsExist labs line ↔ lineGetLabels line ⊆ labsDomain labs := by
  cases line with
  | label k1 k2 len => simp [lineLabsExist,lineGetLabels]
  | asm a bs len => simp [lineLabsExist,lineGetLabels]
  | labAsm a w bs len =>
    change (∀ n1 n2,(n1,n2) ∈ labsOf a → labLookup n1 n2 labs ≠ none) ↔
      (∀ p,p ∈ labsOf a → labLookup p.1 p.2 labs ≠ none)
    constructor
    · intro h p hp
      rcases p with ⟨n1,n2⟩
      exact h n1 n2 hp
    · intro h n1 n2 hp
      exact h (n1,n2) hp

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "sec_labs_exist_get_labels" (words_as_type_indexed_bitvec)]
theorem secLabsExist_iff_labelsSubset {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    secLabsExist labs sec ↔ secGetLabels sec ⊆ labsDomain labs := by
  constructor
  · intro h p hp
    rcases hp with ⟨l,hm,hp⟩
    exact (lineLabsExist_iff_labelsSubset labs l).mp (h l hm) hp
  · intro h l hm
    apply (lineLabsExist_iff_labelsSubset labs l).mpr
    intro p hp
    exact h ⟨l,hm,hp⟩

/-- HOL binds labs and code freely in this full iff; both remain explicit. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "all_labs_exist_get_labels" (words_as_type_indexed_bitvec)]
theorem allLabsExist_iff_labelsSubset {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allLabsExist labs code ↔ getLabels code ⊆ labsDomain labs := by
  constructor
  · intro h p hp
    rcases hp with ⟨sec,hm,hp⟩
    exact (secLabsExist_iff_labelsSubset labs sec).mp (h sec hm) hp
  · intro h sec hm
    apply (secLabsExist_iff_labelsSubset labs sec).mpr
    intro p hp
    exact h ⟨sec,hm,hp⟩
end Flapjack.Compiler.Backend.LabToTarget
