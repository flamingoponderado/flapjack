import Flapjack.Compiler.Backend.LabToTarget.SectionNopEncoding
import Flapjack.Compiler.Backend.LabToTarget.PaddingLengthProps
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original code-padding invariant with the conditional non-single-byte
alignment guard, every source section predicate and actual positional encoding.
Section advancement is proved from the original padding length laws. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_with_nop_pad_code"
  (words_as_type_indexed_bitvec)]
theorem allEncWithNop_padCode {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (nop : List (BitVec 8))
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) :
    0 < nop.length ∧ nop = enc (.inst .skip) ∧
    (nop.length ≠ 1 → (∀ sec ∈ code, secAligned nop.length sec) ∧ (∀ sec ∈ code, secLabelZero sec)) ∧
    (∀ sec ∈ code, secLabelOne sec) ∧ allLengthLeq code ∧
    (∀ sec ∈ code, secLabelPrefixZero sec) ∧ allEncd enc labs ffis pos code →
    allEncWithNop enc labs ffis pos (padCode nop code) := by
  induction code generalizing pos with
  | nil => simp [padCode,allEncWithNop]
  | cons sec rest ih =>
    rintro ⟨hpos,hnop,hcond,hl,hbound,hprefix,he⟩
    rcases sec with ⟨id,lines⟩
    have hlsec := hl ⟨id,lines⟩ (by simp)
    have hbsec := hbound ⟨id,lines⟩ (by simp)
    have hpsec := hprefix ⟨id,lines⟩ (by simp)
    rcases he with ⟨hesec,herest⟩
    have ht := ih (pos + (lines.map lineLen).sum)
      ⟨hpos,hnop,fun hne =>
        ⟨fun s hm => (hcond hne).1 s (by simp [hm]),
         fun s hm => (hcond hne).2 s (by simp [hm])⟩,
       fun s hm => hl s (by simp [hm]),
       fun s hm => hbound s (by simp [hm]),
       fun s hm => hprefix s (by simp [hm]),herest⟩
    have hfirst : linesEncWithNop enc labs ffis pos (padSection nop lines []) := by
      by_cases hone : nop.length = 1
      · apply linesEncWithNop_padSection enc labs ffis nop lines [] pos
        exact ⟨hnop,hone,by simpa using hesec,trivial,by simp,hlsec,hpsec⟩
      · have hc := hcond hone
        apply linesEncWithNop_padSection0 enc labs ffis nop lines [] pos
        exact ⟨hnop,hpos,hc.1 ⟨id,lines⟩ (by simp),by simpa using hesec,
          trivial,by simp,hc.2 ⟨id,lines⟩ (by simp)⟩
    have hlen : ((padSection nop lines []).map lineLength).sum = (lines.map lineLen).sum := by
      by_cases hone : nop.length = 1
      · simpa using lineLength_padSection_labels nop lines []
          ⟨hone,hlsec,hbsec,rfl,by simp,hpsec⟩
      · have hz := (hcond hone).2 ⟨id,lines⟩ (by simp)
        simpa using congrArg List.sum (lineLength_padSection_zero nop lines []
          ⟨hpos,hz,rfl,hbsec⟩)
    rw [padCode]
    apply (allEncWithNop_alt enc labs ffis pos id (padSection nop lines []) (padCode nop rest)).2.mpr
    exact ⟨hfirst,by simpa only [hlen] using ht⟩
end Flapjack.Compiler.Backend.LabToTarget
