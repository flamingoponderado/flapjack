import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Compiler.Backend.LabToTarget.StateRel
import Flapjack.Compiler.Backend.LabToTarget.InstUpdates

/-! Original comparison transport for `JumpCmp` (lab_to_targetProofScript.sml
2983-3025): an even label offset from an even base stays even, so the source
`Test` on a code location agrees with the target test of its address. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem

/-- `1w && w = 0w` is evenness of the numeral; Flapjack infrastructure. -/
theorem one_and_eq_zero_iff {width : Nat} [NeZero width] (w : BitVec width) :
    ((1 : BitVec width) &&& w) = 0 ↔ w.toNat % 2 = 0 := by
  have h1 : (1 : BitVec width).toNat = 1 := by
    have : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    change (BitVec.ofNat width 1).toNat = 1
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  rw [← BitVec.toNat_inj, BitVec.toNat_and, h1, Nat.one_and_eq_mod_two]
  simp

theorem even_add_and {width : Nat} [NeZero width] (p : BitVec width) (x : Nat) :
    ((1 : BitVec width) &&& p) = 0 ∧ x % 2 = 0 →
    ((1 : BitVec width) &&& (p + BitVec.ofNat width x)) = 0 := by
  rintro ⟨hp, hx⟩
  rw [one_and_eq_zero_iff] at hp ⊢
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have h2 : 2 ∣ 2 ^ width := ⟨2 ^ (width - 1), by
    rw [← Nat.pow_succ']; congr 1; omega⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ h2, Nat.add_mod,
    Nat.mod_mod_of_dvd _ h2, hp, hx]

theorem wordCmp_lemma {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (s1 : LabSem.State width Config F) (t1 : AsmState width) (ms1 : S)
    (cmp : HolCmp) (rr : Nat) (ri : HolRegImm width) (x : Bool) :
    stateRel (mc, code2, labs, p) s1 t1 ms1 ∧
      wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) = some x →
    x = wordCmpHOL cmp (AsmSem.readReg rr t1) (AsmSem.regImm ri t1) := by
  rintro ⟨hrel, hc⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ceven, cp, -, -, -, -, -,
    -, -, -, c30, -⟩ := hrel
  have hw : ∀ r w, s1.regs r = .word w → t1.regs r = w :=
    fun r w e => wordLocVal_word_target (c30 r) e
  have hri : ∀ w, LabSem.regImm ri s1 = .word w → AsmSem.regImm ri t1 = w := by
    intro w e
    cases ri with
    | reg r' => exact hw r' w (by simpa [LabSem.regImm] using e)
    | imm v => simpa [LabSem.regImm, AsmSem.regImm] using e
  cases h1 : s1.regs rr with
  | word w1 =>
    cases h2 : LabSem.regImm ri s1 with
    | word w2 =>
      rw [h1, h2] at hc
      simp only [wordSemWordCmp, Option.some.injEq] at hc
      rw [← hc, AsmSem.readReg, hw rr w1 h1, hri w2 h2]
    | loc _ _ => rw [h1, h2] at hc; cases cmp <;> simp [wordSemWordCmp] at hc
  | loc k1 k2 =>
    cases h2 : LabSem.regImm ri s1 with
    | loc _ _ => rw [h1, h2] at hc; cases cmp <;> simp [wordSemWordCmp] at hc
    | word w2 =>
      rw [h1, h2] at hc
      have hv := c30 rr
      rw [h1] at hv
      cases hl : labLookup k1 k2 labs with
      | none => simp [wordLocVal, hl] at hv
      | some q =>
        simp only [wordLocVal, hl, Option.some.injEq] at hv
        have hev := even_add_and p q ⟨cp, ceven k1 k2 q hl⟩
        rw [BitVec.and_comm] at hev
        cases cmp <;> simp only [wordSemWordCmp] at hc <;>
          (try split at hc) <;> (try split at hc) <;> simp at hc
        all_goals
          rename_i hw1
          rw [hc, AsmSem.readReg, ← hv, hri w2 h2, hw1]
          have hev' : (p + BitVec.ofNat width q &&& 1#width) = 0#width := hev
          simp [wordCmpHOL, AndOp.and, hev']

end Flapjack.Compiler.Backend.LabToTarget
