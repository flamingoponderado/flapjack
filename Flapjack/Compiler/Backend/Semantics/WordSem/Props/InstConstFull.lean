import Flapjack.Compiler.Backend.Semantics.WordSem.Props.InstConst

namespace Flapjack.WordSemInstConstFullSupport

/-- Canonical roundtrip for the actual instruction state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end Flapjack.WordSemInstConstFullSupport

namespace Flapjack.WordSemStateFiniteExact

/-- Complete HOL instruction constancy contract (wordProps900-920), including
all thirteen original fields, arbitrary instructions, and the sole successful
instruction premise. This structural invariant inherits reals_as_rational_cuts
from inst; it establishes no cross-language numerical FP correspondence. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem instConstFull {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (state next : WordSemStateFiniteExact width C F)
    (h : inst i state = some next) :
    next.code = state.code ∧
    next.codeBuffer = state.codeBuffer ∧
    next.dataBuffer = state.dataBuffer ∧
    next.compile = state.compile ∧
    next.compileOracle = state.compileOracle ∧
    next.clock = state.clock ∧
    next.ffi = state.ffi ∧
    next.handler = state.handler ∧
    next.stack = state.stack ∧
    next.localsSize = state.localsSize ∧
    next.stackLimit = state.stackLimit ∧
    next.stackMax = state.stackMax ∧
    next.stackSize = state.stackSize := by
  unfold inst at h
  repeat' split at h
  all_goals (try dsimp only at h)
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [reduceCtorEq] at h; done)
    | (cases h; simp [setVar])
    | (simp only [Option.some.injEq] at h; subst h; simp [setVar])
    | (unfold assign at h; split at h
       · cases h
       · cases h; simp [setVar])
    | (rename_i heq; cases h
       unfold memStore at heq
       split at heq <;> cases heq <;> simp)

end Flapjack.WordSemStateFiniteExact
