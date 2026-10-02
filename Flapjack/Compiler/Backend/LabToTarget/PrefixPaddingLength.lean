import Flapjack.Compiler.Backend.LabToTarget.PaddingLengthProps
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original annotation conservation with its conditional prefix guard.
Empty/all-label accumulators are admitted; no nonlabel premise is added. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_pad_section"
  (words_as_type_indexed_bitvec)]
theorem lineLen_padSection_prefix {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (xs aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    nop.length = 1 ∧ (∀ line ∈ xs,labelOne line) ∧
    ((∀ line ∈ aux,isLabelHOL line = true) → labelPrefixZero xs) →
    ((padSection nop xs aux).map lineLen).sum = (xs.map lineLen).sum + (aux.map lineLen).sum := by
  induction xs generalizing aux with
  | nil => simp [padSection]
  | cons line tail ih =>
    rintro ⟨hnop,hxs,hprefix⟩
    by_cases hall : ∀ line ∈ aux,isLabelHOL line = true
    · have hp := hprefix hall
      have ht : ∀ line ∈ tail,labelOne line := fun l hm => hxs l (by simp [hm])
      cases line with
      | label k1 k2 len =>
        have hplen : len = 0 ∧ labelPrefixZero tail := by simpa [isLabelHOL,lineLen] using hp
        have hr := ih (.label k1 k2 0 :: aux) ⟨hnop,ht,fun _ => hplen.2⟩
        simpa [padSection,hplen.1,lineLen] using hr
      | asm a bs len =>
        have hr := lineLen_padSection_nonlabel nop tail (.asm a (padBytes bs len nop) len :: aux)
          ⟨hnop,ht,by simp [isLabelHOL]⟩
        simp only [padSection,List.map_cons,List.sum_cons,lineLen] at hr ⊢
        omega
      | labAsm a w bs len =>
        have hr := lineLen_padSection_nonlabel nop tail (.labAsm a w (padBytes bs len nop) len :: aux)
          ⟨hnop,ht,by simp [isLabelHOL]⟩
        simp only [padSection,List.map_cons,List.sum_cons,lineLen] at hr ⊢
        omega
    · exact lineLen_padSection_nonlabel nop (line :: tail) aux ⟨hnop,hxs,hall⟩
end Flapjack.Compiler.Backend.LabToTarget
