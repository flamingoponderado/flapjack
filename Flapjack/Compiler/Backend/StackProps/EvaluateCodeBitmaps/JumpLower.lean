import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Seq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

namespace JumpLowerCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end JumpLowerCase

/-- Full JumpLower case of the original theorem. The callee IH is guarded by
actual word reads, successful lower comparison, code lookup and nonzero clock;
it applies only at decClock source. No arbitrary-state IH or target/poststate
fact is supplied. The native evaluator closure inherits reals_as_rational_cuts;
no numeric alignment/FP correspondence is asserted. Parent assembly is open. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsJumpLower {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 dest : Nat) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : ∀ (x y : BitVec width) (prog : HolProg width),
      StackSemStateOps.getVar r1 source = some (.word x) →
      StackSemStateOps.getVar r2 source = some (.word y) →
      wordCmpHOL .lower x y = true →
      StackSemControl.findCode (.inl dest) source.regs source.code = some prog →
      source.clock ≠ 0 →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock source) = (res, out) →
      CodeBitmaps (StackSemStateOps.decClock source) out)
    (execution : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) = (result, post)) :
    CodeBitmaps source post := by
  classical
  rw [StackSemEvaluate.evaluate_jumpLower] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals first
    | exact calleeIH _ _ _ (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) _ _ (by assumption)
    | (refine ⟨0, rfl, ?_, ?_⟩ <;> dsimp [StackSemStateOps.emptyEnv] <;> simp)

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
