import Flapjack.Compiler.Encoders.Arm8.Machine.Target
import Flapjack.Compiler.Encoders.Arm8.TargetProof
import Flapjack.Compiler.Encoders.AsmProps.Encoding

/-!
# Structural facts about the closed ARMv8 target

This module proves the projection-consistency half of `target_ok` for the
closed ARMv8 target.  The remaining `enc_ok` proof and the transition
simulation are developed separately.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-- Membership in the projected memory graph. -/
theorem arm8Proj_memory (d : BitVec 64 → Prop) (s : Arm8State)
    (a : BitVec 64) (b : BitVec 8) :
    (arm8Proj d s).2.2.2.2 (a, b) ↔ s.mem a = b ∧ d a := by
  exact SetSep.fun2SetThm s.mem d a b

/-- Projection consistency: equal projections give equal readable state. -/
theorem arm8TargetOkProjection (ms1 ms2 : Arm8State) (s : AsmState 64)
    (h : arm8Proj s.memDomain ms1 = arm8Proj s.memDomain ms2) :
    (targetStateRel arm8Target s ms1 ↔ targetStateRel arm8Target s ms2) ∧
      arm8StateOk ms1 = arm8StateOk ms2 ∧
      ms1.pc = ms2.pc ∧
      (∀ a, s.memDomain a → ms1.mem a = ms2.mem a) := by
  have hpc : ms1.pc = ms2.pc := congrArg Prod.fst h
  have hfailed : ms1.failed = ms2.failed := congrArg (fun p => p.2.2.1) h
  have hregs : ms1.regs = ms2.regs := congrArg (fun p => p.2.2.2.1) h
  have hmem : (arm8Proj s.memDomain ms1).2.2.2.2 =
      (arm8Proj s.memDomain ms2).2.2.2.2 := congrArg (fun p => p.2.2.2.2) h
  have hget (a : BitVec 64) (ha : s.memDomain a) : ms1.mem a = ms2.mem a := by
    have hleft : (arm8Proj s.memDomain ms1).2.2.2.2 (a, ms1.mem a) := by
      rw [arm8Proj_memory]
      exact ⟨rfl, ha⟩
    rw [congrFun hmem (a, ms1.mem a)] at hleft
    rw [arm8Proj_memory] at hleft
    exact hleft.1.symm
  have hok : arm8StateOk ms1 = arm8StateOk ms2 := by
    simp only [arm8StateOk, hpc, hfailed]
  refine ⟨?_, hok, hpc, hget⟩
  simp only [targetStateRel, arm8Target_getPc, arm8Target_getReg, arm8Target_getByte, arm8Target_stateOk, arm8Target_getFpReg, arm8Target_config, hok]
  constructor
  · intro hs
    rcases hs with ⟨hok1, hpc1, hmem1, hreg1, hfp1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hok] using hok1
    · simpa [hpc] using hpc1
    · intro a ha
      rw [← hget a ha]
      exact hmem1 a ha
    · intro i hi
      rw [← hregs]
      exact hreg1 i hi
    · intro i hi
      simp [arm8Config] at hi
  · intro hs
    rcases hs with ⟨hok1, hpc1, hmem1, hreg1, hfp1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hok] using hok1
    · simpa [hpc] using hpc1
    · intro a ha
      rw [hget a ha]
      exact hmem1 a ha
    · intro i hi
      rw [hregs]
      exact hreg1 i hi
    · intro i hi
      simp [arm8Config] at hi

/-- `Loc` byte-length monotonicity, nonnegative offsets. -/
theorem arm8Loc_len_pos (register : Nat) (a1 a2 : BitVec 64)
    (h1 : (0 : BitVec 64).sle a1 = true) (h2 : (0 : BitVec 64).sle a2 = true)
    (h12 : a1.sle a2 = true) :
    (arm8Enc (.loc register a1)).length ≤ (arm8Enc (.loc register a2)).length := by
  rw [length_arm8Enc, length_arm8Enc]
  rw [BitVec.sle_iff_toInt_le] at h1 h2 h12
  have hz : (0 : BitVec 64).toInt = 0 := rfl
  rw [hz] at h1 h2
  by_cases hf1 : fitsSigned 20 a1 = true <;>
    by_cases hf2 : fitsSigned 20 a2 = true <;>
      simp [arm8Ast_loc, hf1, hf2] <;> try omega
  have hf1n : ¬ (-(2 ^ 19 : Int) ≤ a1.toInt ∧ a1.toInt ≤ 2 ^ 19 - 1) := by
    intro hr
    have := (fitsSigned20_toInt a1).2 hr
    rw [this] at hf1
    contradiction
  have hf2r := (fitsSigned20_toInt a2).1 hf2
  omega

/-- `Loc` byte-length monotonicity, negative offsets. -/
theorem arm8Loc_len_neg (register : Nat) (a1 a2 : BitVec 64)
    (h1 : a1.slt 0 = true) (h2 : a2.slt 0 = true)
    (h21 : a2.sle a1 = true) :
    (arm8Enc (.loc register a1)).length ≤ (arm8Enc (.loc register a2)).length := by
  rw [length_arm8Enc, length_arm8Enc]
  rw [BitVec.slt_iff_toInt_lt] at h1
  rw [BitVec.slt_iff_toInt_lt] at h2
  rw [BitVec.sle_iff_toInt_le] at h21
  have hz : (0 : BitVec 64).toInt = 0 := rfl
  rw [hz] at h1 h2
  by_cases hf1 : fitsSigned 20 a1 = true <;>
    by_cases hf2 : fitsSigned 20 a2 = true <;>
      simp [arm8Ast_loc, hf1, hf2] <;> try omega
  have hf1n : ¬ (-(2 ^ 19 : Int) ≤ a1.toInt ∧ a1.toInt ≤ 2 ^ 19 - 1) := by
    intro hr
    have := (fitsSigned20_toInt a1).2 hr
    rw [this] at hf1
    contradiction
  have hf2r := (fitsSigned20_toInt a2).1 hf2
  omega

/-- `enc_ok` for the closed ARMv8 configuration. -/
theorem arm8EncOk : encOk arm8Config := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · intro instruction
    refine ⟨?_, ?_⟩
    · simpa [arm8Config] using length_arm8Enc_mod instruction
    · simpa [arm8Config] using arm8Enc_nonempty instruction
  · intro w1 w2 _
    constructor <;> intro h <;> rcases h with ⟨_, _, _⟩ <;>
      simp [arm8Config, length_arm8Enc]
  · intro cmp reg ri w1 w2 _
    cases ri <;> constructor <;> intro h <;> rcases h with ⟨_, _, _⟩ <;>
      simp [arm8Config, length_arm8Enc]
  · intro w1 w2 _
    constructor <;> intro h <;> rcases h with ⟨_, _, _⟩ <;>
      simp [arm8Config, length_arm8Enc]
  · intro w1 w2 reg _
    constructor
    · intro h
      rcases h with ⟨h1, h2, h12⟩
      exact arm8Loc_len_pos reg w1 w2 h1 h2 h12
    · intro h
      rcases h with ⟨h1, h2, h21⟩
      exact arm8Loc_len_neg reg w1 w2 h1 h2 h21


/-- `target_ok` follows from the projection proof and `enc_ok` of the ARMv8
configuration. -/
theorem arm8TargetOk : targetOk arm8Target := by
  refine ⟨arm8EncOk, ?_⟩
  intro ms1 ms2 s hproj
  exact arm8TargetOkProjection ms1 ms2 s hproj

end Flapjack.Compiler.Encoders.Arm8
