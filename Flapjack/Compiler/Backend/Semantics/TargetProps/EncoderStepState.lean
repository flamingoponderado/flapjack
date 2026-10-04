import Flapjack.Compiler.Backend.Semantics.TargetProps.AsmStepEvaluate
import Flapjack.Compiler.Encoders.AsmProps.Assertions.Iteration
import Mathlib.Logic.Relation

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

/-- Constant-step specialization of assertions; local proof infrastructure. -/
private theorem asserts_iterate_end {α : Type} (n : Nat) (f : α → α)
    (s : α) (P Q : α → Prop) (h : asserts n (fun _ => f) s P Q) :
    Q (f^[n + 1] s) := by
  induction n generalizing s with
  | zero => simpa [asserts] using h
  | succ n ih =>
    simpa [Function.iterate_succ_apply] using ih (f s) h.2

/-- Strict-prefix constant-step assertions; local proof infrastructure. -/
private theorem asserts_iterate_prefix {α : Type} (n : Nat) (f : α → α)
    (s : α) (P Q : α → Prop) (h : asserts n (fun _ => f) s P Q)
    (j : Nat) (hj : j < n) : P (f^[j + 1] s) := by
  induction n generalizing s j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simpa using h.1
    | succ j =>
      simpa [Function.iterate_succ_apply] using ih (f s) h.2 j (by omega)

/-- Full original encoder step simulation, including every strict-prefix
encoded-byte/PC/state invariant and every inclusive-prefix out-of-domain byte
invariant. Inherited total holEl/holHd retains shared opaque holHdNil/holArb,
without bounds or fallback. FP semantics transitively inherit the reviewed
rational-cut real translation and the SOUNDNESS item 8 assumption. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encoderCorrectAsmStepStateRel {width : Nat} [NeZero width] {S Q : Type}
    (t : HolAsmTarget width S Q) (s1 s2 : AsmState width) (ms : S) (i : HolAsm width)
    (h : encoderCorrect t ∧ targetStateRel t s1 ms ∧ asmStep t.config s1 i s2) :
    ∃ n,
      targetStateRel t s2 (t.next^[n] ms) ∧
      (∀ j, j < n →
        (∀ pc, pc ∈ allPcs (t.config.encode i).length s1.pc 0 →
          t.getByte (t.next^[j] ms) pc = t.getByte ms pc) ∧
        t.getPc (t.next^[j] ms) ∈
          allPcs (t.config.encode i).length s1.pc t.config.codeAlignment ∧
        t.stateOk (t.next^[j] ms) = true) ∧
      (∀ j x, j ≤ n ∧ ¬ s1.memDomain x →
        t.getByte (t.next^[j] ms) x = t.getByte ms x) := by
  rcases h with ⟨henc, hrel, hstep⟩
  obtain ⟨n, ha, hf⟩ := encoderCorrect_noInterference henc hstep hrel
  refine ⟨n + 1, asserts_iterate_end n t.next ms _ _ ha, ?_, ?_⟩
  · intro j hj
    cases j with
    | zero =>
      refine ⟨fun _ _ => rfl, ?_, hrel.1⟩
      rw [show t.getPc (t.next^[0] ms) = s1.pc by simpa using hrel.2.1]
      rw [allPcs_eq]
      refine ⟨0, ?_, ?_⟩
      · simpa using List.length_pos_iff.mpr
          (encOkNotEmpty t.config i ⟨henc.1.1, hstep.2.2.2.2.2.2⟩)
      · simp
    | succ j =>
      have hp := asserts_iterate_prefix n t.next ms _ _ ha j (by omega)
      exact ⟨hp.2.1, hp.2.2, hp.1⟩
  · intro j x hx
    induction j with
    | zero => rfl
    | succ j ih =>
      have hj : j < n + 1 := by omega
      have hs := asserts2_every (n + 1) ms j (fun x : S => x) t.next
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → t.getByte ms1 x = t.getByte ms2 x)
        ⟨hf, hj⟩
      have hsx := hs x hx.2
      have hprev := ih ⟨by omega, hx.2⟩
      simpa [Function.iterate_succ_apply', Function.comp_def] using hsx.symm.trans hprev

/-- Full original reflexive-transitive assembly-step simulation. RTC uses
Lean's least reflexive-transitive closure; each target
iteration witness is constructed from the full single-step result. Inherited
total holEl/holHd retains shared opaque holHdNil/holArb without bounds/fallback;
FP semantics inherit rational-cut reals and the SOUNDNESS item 8 assumption. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encoderCorrectRtcAsmStepStateRel {width : Nat} [NeZero width] {S Q : Type}
    (t : HolAsmTarget width S Q) (s1 s2 : AsmState width) (ms : S)
    (h : encoderCorrect t ∧ targetStateRel t s1 ms ∧
      Relation.ReflTransGen (fun s1 s2 => ∃ i, asmStep t.config s1 i s2) s1 s2) :
    ∃ n, targetStateRel t s2 (t.next^[n] ms) := by
  rcases h with ⟨henc, hrel, hrtc⟩
  induction hrtc with
  | refl => exact ⟨0, by simpa using hrel⟩
  | @tail s2 s3 hpre hstep ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨i, hi⟩ := hstep
    obtain ⟨m, hm, _, _⟩ := encoderCorrectAsmStepStateRel t _ _ (t.next^[n] ms) i
      ⟨henc, hn, hi⟩
    exact ⟨m + n, by simpa only [Function.iterate_add_apply] using hm⟩

end Flapjack.Compiler.Backend.Semantics.TargetProps
