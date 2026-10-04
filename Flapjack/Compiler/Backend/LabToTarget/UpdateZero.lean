import Flapjack.Compiler.Backend.LabToTarget.UpdatePosition
import Flapjack.Compiler.Backend.LabToTarget.EncodingInvariant
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
import Flapjack.Compiler.Encoders.AsmProps.Encoding
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack-specific arithmetic consequence of the complete original encoder guard. -/
private theorem encodedEven {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (hc : encOk c) (hz : c.codeAlignment ≠ 0)
    (a : HolAsm width) : (c.encode a).length % 2 = 0 := by
  have hd : 2 ∣ 2 ^ c.codeAlignment := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
    rw [hn, Nat.pow_succ]
    exact ⟨2 ^ n, by omega⟩
  have hm := Nat.mod_mod_of_dvd (c.encode a).length hd
  rw [hc.2.1 a |>.1] at hm
  simpa using hm.symm

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesUpdLabLen_encd0LabelZero {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (enc : HolAsm width → List (BitVec 8))
    (pos : Nat) (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    encOk c ∧ enc = c.encode ∧ c.codeAlignment ≠ 0 ∧
      (∀ line ∈ lines, lineEncd0 enc line) ∧ pos % 2 = 0 ∧
      (∀ line ∈ aux, labelZero line) →
    ∀ line ∈ (linesUpdLabLen pos lines aux).1, labelZero line := by
  rintro ⟨hc,rfl,hz,hls,hp,ha⟩
  induction lines generalizing pos aux with
  | nil => simpa [linesUpdLabLen] using ha
  | cons x xs ih =>
    have hx := hls x (by simp)
    have ht : ∀ line ∈ xs, lineEncd0 c.encode line := fun l hm => hls l (by simp [hm])
    cases x with
    | label k1 k2 len =>
      simp only [linesUpdLabLen,if_pos hp,Nat.add_zero]
      exact ih pos (.label k1 k2 0 :: aux) ht hp (by simpa [labelZero] using ha)
    | asm a bs len =>
      have he : len % 2 = 0 := by
        rcases hx with ⟨hb,hl⟩
        rw [hl,← hb]
        exact encodedEven c hc hz _
      simp only [linesUpdLabLen]
      apply ih (pos + len) (.asm a bs len :: aux) ht
      · omega
      · simpa [labelZero] using ha
    | labAsm a w bs len =>
      have he : len % 2 = 0 := by
        rcases hx with ⟨_,_,w',hl⟩
        rw [hl]
        exact encodedEven c hc hz _
      simp only [linesUpdLabLen]
      apply ih (pos + len) (.labAsm a w bs len :: aux) ht
      · omega
      · simpa [labelZero] using ha

/-- Flapjack-specific equivalence of two guarded last-label classifiers. -/
private theorem ends_iff {width : Nat} [NeZero width]
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    secEndsWithLabelNative sec ↔ sec.lines ≠ [] ∧ lastLabel sec.lines = true := by
  unfold secEndsWithLabelNative lastLabel
  rw [List.getLast?_eq_head?_reverse]
  have hn : sec.lines ≠ [] ↔ sec.lines.reverse ≠ [] := by simp
  rw [hn]
  cases sec.lines.reverse <;> simp

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updLabLen_encd0LabelZero {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (enc : HolAsm width → List (BitVec 8))
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encOk c ∧ enc = c.encode ∧ c.codeAlignment ≠ 0 ∧
      allEncd0 enc code ∧ pos % 2 = 0 ∧
      (∀ sec ∈ code, secEndsWithLabelNative sec) →
    ∀ sec ∈ updLabLen pos code, secLabelZero sec := by
  rintro ⟨hc,he,hz,hcode,hp,hends⟩
  induction code generalizing pos with
  | nil => simp [updLabLen]
  | cons sec rest ih =>
    rcases sec with ⟨id,ls⟩
    have hl := linesUpdLabLen_encd0LabelZero c enc pos ls []
      ⟨hc,he,hz,hcode ⟨id,ls⟩ (by simp),hp,by simp⟩
    have hend := (ends_iff ⟨id,ls⟩).mp (hends ⟨id,ls⟩ (by simp))
    have hout := linesUpdLabLen_evenLength pos ls []
      (by simp [hend.1,hend.2,hp])
    have hpos := linesUpdLabLen_position pos ls []
    simp only [List.map_nil,List.sum_nil,Nat.sub_zero] at hpos
    have hp' : (linesUpdLabLen pos ls []).2 % 2 = 0 := by omega
    have hr := ih (linesUpdLabLen pos ls []).2
      (fun s hm => hcode s (by simp [hm])) hp'
      (fun s hm => hends s (by simp [hm]))
    simpa [updLabLen,secLabelZero] using And.intro hl hr
end Flapjack.Compiler.Backend.LabToTarget
