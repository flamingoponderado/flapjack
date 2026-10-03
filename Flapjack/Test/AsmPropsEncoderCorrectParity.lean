import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

namespace Flapjack.Test.AsmPropsEncoderCorrectParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

/-! Kernel replay of `scripts/hol-probes/asm_props_encoder_correct_probe.out`: the two HOL-proved
consumers of `encoder_correct`. -/

-- ec_target_ok=encoder_correct t ⇒ target_ok t
example {width : Nat} [NeZero width] {β γ : Type} (t : HolAsmTarget width β γ) :
    encoderCorrect t → targetOk t := encoderCorrect_targetOk

-- ec_no_interference=encoder_correct t ∧ asm_step t.config s1 i s2 ∧ target_state_rel t s1 ms ⇒ ∃n. asserts n (λk s. t.next s) ms ... ∧ asserts2 (n + 1) (λk x. x) t.next ms ...
example {width : Nat} [NeZero width] {β γ : Type} (t : HolAsmTarget width β γ)
    (s1 s2 : AsmState width) (i : HolAsm width) (ms : β)
    (h : encoderCorrect t ∧ asmStep t.config s1 i s2 ∧ targetStateRel t s1 ms) :
    ∃ n : Nat,
      asserts n (fun _ s => t.next s) ms
          (fun ms' => t.stateOk ms' = true ∧
            (∀ pc, pc ∈ allPcs (t.config.encode i).length s1.pc 0 → t.getByte ms' pc = t.getByte ms pc) ∧
            t.getPc ms' ∈ allPcs (t.config.encode i).length s1.pc t.config.codeAlignment)
          (fun ms' => targetStateRel t s2 ms') ∧
        asserts2 (n + 1) (fun _ x => x) t.next ms
          (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → t.getByte ms1 x = t.getByte ms2 x) :=
  encoderCorrect_noInterference h.1 h.2.1 h.2.2

end Flapjack.Test.AsmPropsEncoderCorrectParity
