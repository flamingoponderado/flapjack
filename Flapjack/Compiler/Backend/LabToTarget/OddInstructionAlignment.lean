import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity
import Flapjack.Compiler.Encoders.AsmProps.Encoding

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Original proof-side classifier, using physical line length, including the
Label length conditional. There is no executed compiler caller in HOL. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def hasOddInst {width : Nat} [NeZero width] :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → Prop
  | [] => False
  | ⟨_,[]⟩::rest => hasOddInst rest
  | ⟨k,line::lines⟩::rest => lineLength line % 2 ≠ 0 ∨ hasOddInst (⟨k,lines⟩::rest)
termination_by code => code.length + (code.map (fun sec => sec.lines.length)).sum
decreasing_by all_goals simp_wf

/-- Flapjack arithmetic infrastructure: the source enc_ok divisibility conjunct
makes every actual NOP-padded byte list even when alignment is nonzero. This
projection has no independently named HOL original. -/
private theorem encWithNop_even {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (instruction : HolAsm width) (bytes : List (BitVec 8))
    (hc : encOk c) (hn : c.codeAlignment ≠ 0) (he : encWithNop c.encode instruction bytes) :
    bytes.length % 2 = 0 := by
  have hd : 2 ∣ 2 ^ c.codeAlignment := by
    cases ha : c.codeAlignment with
    | zero => exact False.elim (hn ha)
    | succ a =>
      rw [Nat.pow_succ]
      exact ⟨2 ^ a,Nat.mul_comm _ _⟩
  have hi : (c.encode instruction).length % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_of_mod_eq_zero (hc.2.1 instruction).1))
  have hs : (c.encode (.inst .skip)).length % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_of_mod_eq_zero (hc.2.1 (.inst .skip)).1))
  obtain ⟨count,he⟩ := (encWithNop_iff c.encode instruction bytes).mp he
  have hlength : (List.replicate count (c.encode (.inst .skip))).flatten.length =
      count * (c.encode (.inst .skip)).length := by
    induction count with
    | zero => simp
    | succ count ih => simp [List.replicate_succ,Nat.succ_mul,Nat.add_comm]
  rw [he,List.length_append,hlength]
  simp [Nat.add_mod,Nat.mul_mod,hi,hs]

/-- Full original line alignment theorem, retaining exactly encoding contract,
full line validity, and odd physical length. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineOk_alignment {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    encOk c ∧ lineOk c labs ffis pos line ∧ lineLength line % 2 = 1 → c.codeAlignment = 0 := by
  rintro ⟨hc,hv,ho⟩
  apply Classical.byContradiction
  intro hn
  cases line with
  | label sid lid len =>
    have hz : len = 0 := hv.2
    simp [lineLength,hz] at ho
  | asm a bytes len =>
    have he := encWithNop_even c (cbwToAsmHOL a) bytes hc hn hv.1
    simp only [lineLength] at ho
    omega
  | labAsm a w bytes len =>
    cases a <;> simp only [lineOk] at hv
    all_goals try split at hv
    all_goals try contradiction
    all_goals
      have he := encWithNop_even c _ bytes hc hn hv.1
      simp only [lineLength] at ho
      omega

/-- Full original whole-code alignment theorem. Oddness is detected on the
same physical recursion traversed by all_enc_ok; no extra result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem hasOddInst_alignment {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encOk c ∧ allEncOk c labs ffis pos code ∧ hasOddInst code → c.codeAlignment = 0 := by
  induction code generalizing pos with
  | nil => simp [hasOddInst]
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    induction lines generalizing pos with
    | nil =>
      rintro ⟨hc,hv,ho⟩
      rw [allEncOk] at hv
      rw [hasOddInst] at ho
      exact ih pos ⟨hc,hv.2,ho⟩
    | cons line lines ihLines =>
      rintro ⟨hc,hv,ho⟩
      rw [allEncOk] at hv
      rw [hasOddInst] at ho
      rcases ho with ho | ho
      · apply lineOk_alignment c labs ffis pos line
        exact ⟨hc,hv.1,by have hm := Nat.mod_lt (lineLength line) (by omega : 0 < 2); omega⟩
      · exact ihLines (pos + lineLength line) ⟨hc,hv.2,ho⟩
end Flapjack.Compiler.Backend.LabToTarget
