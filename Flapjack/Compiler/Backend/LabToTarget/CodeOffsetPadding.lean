import Flapjack.Compiler.Backend.LabToTarget.OffsetPadding
import Flapjack.Compiler.Backend.LabToTarget.PrefixPaddingLength
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original code padding offset preservation. HOL's free nop variable is
retained explicitly, alongside all five source guards and actual padded code. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "offset_ok_pad_code"
  (words_as_type_indexed_bitvec)]
theorem offsetOk_padCode {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (nop.length ≠ 1 → ∀ sec ∈ code,secLabelZero sec) ∧
    (∀ sec ∈ code,secLabelOne sec) ∧ (∀ sec ∈ code,secLabelPrefixZero sec) ∧
    allLabLenPosOk pos code ∧ offsetOk labs ffis pos code →
      offsetOk labs ffis pos (padCode nop code) := by
  induction code generalizing pos with
  | nil => simp [padCode,offsetOk]
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    rintro ⟨hzero,hone,hprefix,hp,ho⟩
    simp only [allLabLenPosOk] at hp
    simp only [offsetOk] at ho
    have hoone : ∀ l ∈ lines,labelOne l := hone ⟨id,lines⟩ (by simp)
    have hpre : labelPrefixZero lines := hprefix ⟨id,lines⟩ (by simp)
    have hguard : (match (generalizing := false) lines with
        | .label _ _ len :: _ => len = 1 | _ => False) → False := by
      cases lines with
      | nil => simp
      | cons line tail =>
        cases line with
        | label k1 k2 len =>
          have hz : len = 0 ∧ labelPrefixZero tail := by simpa [isLabelHOL,lineLen] using hpre
          simp [hz.1]
        | asm a bs len => simp
        | labAsm a w bs len => simp
    have hline := linesOffsetOk_padSection nop lines [] labs ffis pos
      ⟨by simpa using hp.1,True.intro,by simp,hguard,by simpa using ho.1⟩
    have hs : ((padSection nop lines []).map lineLen).sum = (lines.map lineLen).sum := by
      by_cases hnop : nop.length = 1
      · simpa using lineLen_padSection_prefix nop lines [] ⟨hnop,hoone,fun _ => hpre⟩
      · have hz : ∀ l ∈ lines,labelZero l := hzero hnop ⟨id,lines⟩ (by simp)
        simpa using lineLen_padSection_zero nop lines [] hz
    have hrest := ih (pos+(lines.map lineLen).sum)
      ⟨fun hn s hm => hzero hn s (by simp [hm]),fun s hm => hone s (by simp [hm]),
        fun s hm => hprefix s (by simp [hm]),by simpa [secLengthSumLineLen] using hp.2,ho.2⟩
    simp only [padCode,offsetOk]
    refine ⟨hline,?_⟩
    simpa [hs] using hrest
end Flapjack.Compiler.Backend.LabToTarget
