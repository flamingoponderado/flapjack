import Flapjack.Compiler.Encoders.AsmProps.Assertions
import Flapjack.Compiler.Encoders.AsmProps.Interference
import Flapjack.Compiler.Encoders.AsmProps.Encoding
import Flapjack.Compiler.Encoders.AsmProps.PcCoverage
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.Compiler.Encoders.AsmSem.Step

/-!
# asmProps `encoder_correct`

Port of `encoder_correct_def` (`asmPropsScript.sml:117-133`): a target is correct when its
encoding satisfies `target_ok` and every `asm_step` from a related state is simulated by some
number of target steps under every projection-preserving interference environment, keeping the
encoded bytes and landing on an encoded PC, while never changing bytes outside the source
memory domain. HOL sets are predicates (`pcs 0` and `pcs code_alignment` from the curried
`all_pcs`), `x ∉ s1.mem_domain` is `¬ s1.memDomain x`, and `t.state_ok ms'` is `= true`.
-/

namespace Flapjack.Compiler.Encoders.AsmProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

/-- Exact HOL `encoder_correct_def` (`asmPropsScript.sml:117-133`), with the original binders
`s1 i s2 ms`, `n` and `env`, and the `let pcs = all_pcs ...` binding. -/
@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "encoder_correct_def"
  (words_as_type_indexed_bitvec)]
noncomputable def encoderCorrect {width : Nat} [NeZero width] {β γ : Type}
    (t : HolAsmTarget width β γ) : Prop :=
  targetOk t ∧
    ∀ (s1 : AsmState width) (i : HolAsm width) (s2 : AsmState width) (ms : β),
      asmStep t.config s1 i s2 ∧ targetStateRel t s1 ms →
      ∃ n : Nat, ∀ env : Nat → β → β,
        interferenceOk env (t.proj s1.memDomain) →
        let pcs := allPcs (t.config.encode i).length s1.pc
        asserts n (fun k s => env (n - k) (t.next s)) ms
            (fun ms' => t.stateOk ms' = true ∧
              (∀ pc, pc ∈ pcs 0 → t.getByte ms' pc = t.getByte ms pc) ∧
              t.getPc ms' ∈ pcs t.config.codeAlignment)
            (fun ms' => targetStateRel t s2 ms') ∧
          asserts2 (n + 1) (fun k => env (n + 1 - k)) t.next ms
            (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → t.getByte ms1 x = t.getByte ms2 x)

/-- An encoder-correct target is `target_ok` (Flapjack infrastructure; HOL proves the same
projection in `asm_props_encoder_correct_probe`). -/
theorem encoderCorrect_targetOk {width : Nat} [NeZero width] {β γ : Type}
    {t : HolAsmTarget width β γ} (h : encoderCorrect t) : targetOk t := h.1

/-- The identity environment preserves every projection, so an encoder-correct target simulates
each step without interference (Flapjack infrastructure; HOL proves the same specialization in
the probe). -/
theorem encoderCorrect_noInterference {width : Nat} [NeZero width] {β γ : Type}
    {t : HolAsmTarget width β γ} (h : encoderCorrect t) {s1 s2 : AsmState width}
    {i : HolAsm width} {ms : β} (hs : asmStep t.config s1 i s2) (hr : targetStateRel t s1 ms) :
    ∃ n : Nat,
      asserts n (fun _ s => t.next s) ms
          (fun ms' => t.stateOk ms' = true ∧
            (∀ pc, pc ∈ allPcs (t.config.encode i).length s1.pc 0 → t.getByte ms' pc = t.getByte ms pc) ∧
            t.getPc ms' ∈ allPcs (t.config.encode i).length s1.pc t.config.codeAlignment)
          (fun ms' => targetStateRel t s2 ms') ∧
        asserts2 (n + 1) (fun _ x => x) t.next ms
          (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → t.getByte ms1 x = t.getByte ms2 x) := by
  obtain ⟨n, hn⟩ := h.2 s1 i s2 ms ⟨hs, hr⟩
  exact ⟨n, hn (fun _ x => x) (fun _ _ => rfl)⟩

end Flapjack.Compiler.Encoders.AsmProps
