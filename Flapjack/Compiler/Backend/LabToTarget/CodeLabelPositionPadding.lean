import Flapjack.Compiler.Backend.LabToTarget.LabelPositionPadding
import Flapjack.Compiler.Backend.LabToTarget.PrefixPaddingLength
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original code-level padding parity. Both one-byte and arbitrary NOP
branches retain the source guards and actual annotation-based section positions. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allLabLenPosOk_padCode {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) :
    allLabLenPosOk pos code ∧
    (nop.length ≠ 1 → ∀ sec ∈ code,secLabelZero sec) ∧
    (∀ sec ∈ code,secLabelOne sec) ∧ (∀ sec ∈ code,secLabelPrefixZero sec) →
      allLabLenPosOk pos (padCode nop code) := by
  induction code generalizing pos with
  | nil => simp [padCode,allLabLenPosOk]
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    rintro ⟨hp,hzero,hone,hprefix⟩
    simp only [allLabLenPosOk] at hp
    have ho : ∀ l ∈ lines,labelOne l := hone ⟨id,lines⟩ (by simp)
    have hpre : labelPrefixZero lines := hprefix ⟨id,lines⟩ (by simp)
    have hline := padSection_posOk nop lines [] pos
      ⟨by simpa using hp.1,True.intro,by simp,fun _ => hpre⟩
    have hs : ((padSection nop lines []).map lineLen).sum = (lines.map lineLen).sum := by
      by_cases hnop : nop.length = 1
      · simpa using lineLen_padSection_prefix nop lines [] ⟨hnop,ho,fun _ => hpre⟩
      · have hz : ∀ l ∈ lines,labelZero l := hzero hnop ⟨id,lines⟩ (by simp)
        simpa using lineLen_padSection_zero nop lines [] hz
    have hrest := ih (pos+secLength lines 0)
      ⟨hp.2,fun hn s hm => hzero hn s (by simp [hm]),
        fun s hm => hone s (by simp [hm]),fun s hm => hprefix s (by simp [hm])⟩
    simp only [padCode,allLabLenPosOk]
    refine ⟨hline,?_⟩
    simpa [secLengthSumLineLen,hs] using hrest
end Flapjack.Compiler.Backend.LabToTarget
