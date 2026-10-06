import Flapjack.Mips32.TargetProof.Control

/-! # `encoder_correct mips32Target`

The MIPS32 target satisfies CakeML's `encoder_correct` (`asmPropsScript.sml`): `target_ok`
and the simulation of every asm instruction by Ziren's ISA model, under every interference
environment that preserves the projection. This is the obligation `mc_conf_ok` asks of a
machine configuration, so it is what instantiates the Pancake-to-target theorem at MIPS32.

Flapjack-specific: it is the analogue of HOL's `mips_encoder_correct`
(`cakeml/compiler/encoders/mips/proofs/mips_targetProofScript.sml`), which is about the
MIPS64 L3 model, so it carries no `@[hol]` tag. -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

theorem len_jump (a : W) : (mips32Enc (.jump a)).length = if shortRange 4 a then 8 else 28 := by
  rw [mips32Enc_length]; by_cases h : shortRange 4 a = true <;> simp [mips32Ast, h]
theorem len_call (a : W) : (mips32Enc (.call a)).length = if shortRange 4 a then 8 else 24 := by
  rw [mips32Enc_length]; by_cases h : shortRange 4 a = true <;> simp [mips32Ast, h]

theorem short_mono_pos (a1 a2 : W) (h0 : BitVec.sle 0 a1 = true) (h12 : BitVec.sle a1 a2 = true)
    (h : shortRange 4 a2 = true) : shortRange 4 a1 = true := by
  simp only [shortRange, BitVec.sle, Bool.and_eq_true, decide_eq_true_eq] at *
  have : (0 : W).toInt = 0 := by decide
  omega

theorem short_mono_neg (a1 a2 : W) (h0 : BitVec.slt a1 0 = true) (h12 : BitVec.sle a2 a1 = true)
    (h : shortRange 4 a2 = true) : shortRange 4 a1 = true := by
  simp only [shortRange, BitVec.sle, BitVec.slt, Bool.and_eq_true, decide_eq_true_eq] at *
  have : (0 : W).toInt = 0 := by decide
  omega

theorem mips32_encOk : encOk mips32Config := by
  refine ⟨rfl, fun i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [show mips32Config.encode = mips32Enc from rfl, mips32Enc_length]
    have := mips32Ast_ne_nil i
    refine ⟨by simp [mips32Config], by have := List.length_pos_iff.mpr this; omega⟩
  · intro w1 w2 _
    refine ⟨fun hh => ?_, fun hh => ?_⟩ <;> obtain ⟨h0, -, h12⟩ := hh <;>
      simp only [show mips32Config.encode = mips32Enc from rfl, len_jump]
    · by_cases h : shortRange 4 w2 = true
      · simp [h, short_mono_pos w1 w2 h0 h12 h]
      · simp [h]; split <;> omega
    · by_cases h : shortRange 4 w2 = true
      · simp [h, short_mono_neg w1 w2 h0 h12 h]
      · simp [h]; split <;> omega
  · intro c r ri w1 w2 _
    have : (mips32Enc (.jumpCmp c r ri w1)).length = (mips32Enc (.jumpCmp c r ri w2)).length := by
      rw [mips32Enc_length, mips32Enc_length]
      cases ri <;> cases c <;> simp [mips32Ast]
    simp only [show mips32Config.encode = mips32Enc from rfl, this]
    exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩
  · intro w1 w2 _
    refine ⟨fun hh => ?_, fun hh => ?_⟩ <;> obtain ⟨h0, -, h12⟩ := hh <;>
      simp only [show mips32Config.encode = mips32Enc from rfl, len_call]
    · by_cases h : shortRange 4 w2 = true
      · simp [h, short_mono_pos w1 w2 h0 h12 h]
      · simp [h]; split <;> omega
    · by_cases h : shortRange 4 w2 = true
      · simp [h, short_mono_neg w1 w2 h0 h12 h]
      · simp [h]; split <;> omega
  · intro w1 w2 r _
    have : (mips32Enc (.loc r w1)).length = (mips32Enc (.loc r w2)).length := by
      rw [mips32Enc_length, mips32Enc_length]
      by_cases h : r = 31 <;> simp [mips32Ast, h]
    simp only [show mips32Config.encode = mips32Enc from rfl, this]
    exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩

theorem mips32_targetOk : targetOk mips32Target := by
  refine ⟨mips32_encOk, fun ms1 ms2 s hp => ?_⟩
  have h := (proj_eq_iff _ _ _).1 hp
  refine ⟨⟨fun hr => targetStateRel_congr h.symm hr, fun hr => targetStateRel_congr h hr⟩,
    mips32Ok_congr h, h.pc, fun a ha => h.mem a ha⟩

/-- `encoder_correct` for the MIPS32 target over Ziren's ISA model: `target_ok` and every
source instruction, every interference environment, both assertions. -/
theorem mips32_encoder_correct : encoderCorrect mips32Target := by
  refine ⟨mips32_targetOk, ?_⟩
  intro s1 i s2 ms h
  cases i with
  | inst v =>
    cases v with
    | skip => exact case_skip s1 s2 ms h
    | const r c => exact case_const r c s1 s2 ms h
    | arith a =>
      cases a with
      | binop op r t right =>
        cases right with
        | reg u => exact case_binop_reg op r t u s1 s2 ms h
        | imm w => exact case_binop_imm op r t w s1 s2 ms h
      | shift op r t right =>
        cases right with
        | reg u => exact case_shift_reg op r t u s1 s2 ms h
        | imm w => exact case_shift_imm op r t w s1 s2 ms h
      | div r t u => exact case_div r t u s1 s2 ms h
      | longMul r t u v => exact case_longMul r t u v s1 s2 ms h
      | longDiv r t u v q => exact case_longDiv r t u v q s1 s2 ms h
      | addCarry r t u v => exact case_addCarry r t u v s1 s2 ms h
      | addOverflow r t u v => exact case_addOverflow r t u v s1 s2 ms h
      | subOverflow r t u v => exact case_subOverflow r t u v s1 s2 ms h
    | mem m r address =>
      cases address with
      | addr base w =>
        cases m with
        | load => exact case_load r base w s1 s2 ms h
        | load8 => exact case_load8 r base w s1 s2 ms h
        | load16 => exact case_load16 r base w s1 s2 ms h
        | load32 => exact case_load32 r base w s1 s2 ms h
        | store => exact case_store r base w s1 s2 ms h
        | store8 => exact case_store8 r base w s1 s2 ms h
        | store16 => exact case_store16 r base w s1 s2 ms h
        | store32 => exact case_store32 r base w s1 s2 ms h
    | fp f => exact case_fp f s1 s2 ms h
  | jump a => exact case_jump a s1 s2 ms h
  | jumpCmp c r right a =>
    cases right with
    | reg u => exact case_jumpCmp_reg c r u a s1 s2 ms h
    | imm w => exact case_jumpCmp_imm c r w a s1 s2 ms h
  | call a => exact case_call a s1 s2 ms h
  | jumpReg r => exact case_jumpReg r s1 s2 ms h
  | loc r c => exact case_loc r c s1 s2 ms h

end Flapjack.Mips32.TargetProof
