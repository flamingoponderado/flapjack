import Flapjack.Compiler.Backend.LabToTarget.BytesInMemoryFetch
import Flapjack.Compiler.Backend.LabToTarget.OddInstructionAlignment
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect
import Flapjack.Compiler.Backend.LabToTarget.InstAlignment

/-! Original code-alignment of instruction positions
(lab_to_targetProofScript.sml:2934-2981, 6541-6548): every valid line has a
length divisible by `2 ** code_alignment`, hence so has every position. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.AsmProps

/-- Padded encodings have lengths divisible by the code alignment; Flapjack
infrastructure for the `enc_ok_def`/`enc_with_nop_thm` step. -/
theorem encWithNop_length_mod {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (i : HolAsm width) (bytes : List (BitVec 8)) (hc : encOk c)
    (he : encWithNop c.encode i bytes) : bytes.length % 2 ^ c.codeAlignment = 0 := by
  obtain ⟨count, rfl⟩ := (encWithNop_iff c.encode i bytes).mp he
  have hi := (hc.2.1 i).1
  have hs := (hc.2.1 (.inst .skip)).1
  have hlength : (List.replicate count (c.encode (.inst .skip))).flatten.length =
      count * (c.encode (.inst .skip)).length := by simp
  rw [List.length_append, hlength, Nat.add_mod, hi, Nat.mul_mod, hs]
  simp

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_MOD_0"
  (words_as_type_indexed_bitvec)]
theorem lineLength_mod_zero {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (p : Nat) (h : LabLineHOL width) :
    encoderCorrect mc.target ∧ (p % 2 ≠ 0 → mc.target.config.codeAlignment = 0) ∧
      lineOk mc.target.config labs ffis p h →
    lineLength h % 2 ^ mc.target.config.codeAlignment = 0 := by
  rintro ⟨hec, -, hok⟩
  have hc : encOk mc.target.config := hec.1.1
  cases h with
  | label _ _ l =>
    simp only [lineOk] at hok
    simp [lineLength, hok.2]
  | asm b bytes len =>
    simp only [lineOk] at hok
    exact encWithNop_length_mod _ _ _ hc hok.1
  | labAsm a w bytes len =>
    simp only [lineLength]
    cases a with
    | jump t =>
      exact encWithNop_length_mod _ _ _ hc
        (lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inl ⟨t, rfl⟩) hok).1
    | jumpCmp cmp r ri t =>
      exact encWithNop_length_mod _ _ _ hc
        (lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inl ⟨cmp, r, ri, t, rfl⟩)) hok).1
    | locValue r t =>
      exact encWithNop_length_mod _ _ _ hc
        (lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨r, t, rfl⟩)) hok).1
    | call t => simp [lineOk] at hok
    | halt => simp only [lineOk] at hok; exact encWithNop_length_mod _ _ _ hc hok.1
    | install => simp only [lineOk] at hok; exact encWithNop_length_mod _ _ _ hc hok.1
    | callFFI s => simp only [lineOk] at hok; exact encWithNop_length_mod _ _ _ hc hok.1

/-- Odd-line obligations descend past the first line; Flapjack infrastructure
for the `has_odd_inst_def` steps of `pos_val_MOD_0`. -/
theorem posVal_step_odd {width : Nat} [NeZero width] {P : Prop} {k : Nat}
    {y : LabLineHOL width} {ys : List (LabLineHOL width)} {xs : LabProgHOL width}
    (hodd : hasOddInst (⟨k, y :: ys⟩ :: xs) → P) : hasOddInst (⟨k, ys⟩ :: xs) → P :=
  fun h => hodd (by rw [hasOddInst]; exact Or.inr h)

theorem posVal_step_even {width : Nat} [NeZero width] {P : Prop} {k pos : Nat}
    {y : LabLineHOL width} {ys : List (LabLineHOL width)} {xs : LabProgHOL width}
    (hodd : hasOddInst (⟨k, y :: ys⟩ :: xs) → P) (hev : pos % 2 ≠ 0 → P) :
    (pos + lineLength y) % 2 ≠ 0 → P := by
  intro h
  by_cases hl : lineLength y % 2 = 0
  · exact hev (by omega)
  · exact hodd (by rw [hasOddInst]; exact Or.inl hl)

theorem posVal_step_mod {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    {pos : Nat} {y : LabLineHOL width} (hec : encoderCorrect mc.target)
    (hev : pos % 2 ≠ 0 → mc.target.config.codeAlignment = 0)
    (hmod : pos % 2 ^ mc.target.config.codeAlignment = 0)
    (hok : lineOk mc.target.config labs ffis pos y) :
    (pos + lineLength y) % 2 ^ mc.target.config.codeAlignment = 0 := by
  rw [Nat.add_mod, hmod, lineLength_mod_zero mc labs ffis pos y ⟨hec, hev, hok⟩]
  simp

/-- HOL's `val pos_val_MOD_0` (lab_to_targetProofScript.sml:2955-2979), a
`Q.prove` binding with no theorem name; its general-offset form before the
source specializes the starting position to `0`. -/
theorem posVal_mod_zero_gen {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (x pos : Nat) (code2 : LabProgHOL width) :
    encoderCorrect mc.target ∧ (hasOddInst code2 → mc.target.config.codeAlignment = 0) ∧
      (pos % 2 ≠ 0 → mc.target.config.codeAlignment = 0) ∧
      pos % 2 ^ mc.target.config.codeAlignment = 0 ∧
      allEncOk mc.target.config labs ffis pos code2 →
    posVal x pos code2 % 2 ^ mc.target.config.codeAlignment = 0 := by
  rintro ⟨hec, hodd, hev, hmod, henc⟩
  fun_induction posVal x pos code2 with
  | case1 => exact hmod
  | case2 _ pos _ xs ih =>
    rw [allEncOk] at henc
    exact ih (by intro h; exact hodd (by simpa [hasOddInst] using h)) hev hmod henc.2
  | case3 i pos k y ys xs hy ih =>
    rw [allEncOk] at henc
    exact ih (posVal_step_odd hodd) (posVal_step_even hodd hev)
      (posVal_step_mod mc labs ffis hec hev hmod henc.1) henc.2
  | case4 => exact hmod
  | case5 i pos k y ys xs hy hi ih =>
    rw [allEncOk] at henc
    exact ih (posVal_step_odd hodd) (posVal_step_even hodd hev)
      (posVal_step_mod mc labs ffis hec hev hmod henc.1) henc.2

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "all_enc_ok_aligned_pos_val" (words_as_type_indexed_bitvec)]
theorem allEncOk_aligned_posVal {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (code2 : LabProgHOL width)
    (pc : Nat) (ffis : List HolFfiName) :
    allEncOk mc.target.config labs ffis 0 code2 ∧
      (hasOddInst code2 → mc.target.config.codeAlignment = 0) ∧
      encoderCorrect mc.target →
    holAligned mc.target.config.codeAlignment
      (BitVec.ofNat width (posVal pc 0 code2)) = true := by
  rintro ⟨henc, hodd, hec⟩
  have hm := posVal_mod_zero_gen mc labs ffis pc 0 code2
    ⟨hec, hodd, by simp, by simp, henc⟩
  rw [holAligned_iff, BitVec.toNat_ofNat]
  set a := mc.target.config.codeAlignment
  set n := posVal pc 0 code2
  rcases Nat.le_total a width with h | h
  · rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]; exact hm
  · have : n % 2 ^ width = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 h) (Nat.dvd_of_mod_eq_zero hm))
    rw [this]; simp

end Flapjack.Compiler.Backend.LabToTarget
