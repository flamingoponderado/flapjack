import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc

namespace Flapjack.WordSemGcConstSupport

/-- Canonical roundtrip for the native garbage-collector state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end Flapjack.WordSemGcConstSupport

namespace Flapjack.WordSemStateFiniteExact

/-- Complete original gc_const contract (wordProps612-630), retaining all
thirteen conclusions and only the successful-collection premise. Arbitrary
GC callbacks and stack-decoding outcomes are covered without callback laws. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gcConst {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F)
    (h : gc state = some next) :
    next.clock = state.clock ∧
    next.ffi = state.ffi ∧
    next.code = state.code ∧
    next.be = state.be ∧
    next.codeBuffer = state.codeBuffer ∧
    next.dataBuffer = state.dataBuffer ∧
    next.compile = state.compile ∧
    next.handler = state.handler ∧
    next.compileOracle = state.compileOracle ∧
    next.localsSize = state.localsSize ∧
    next.stackLimit = state.stackLimit ∧
    next.stackMax = state.stackMax ∧
    next.stackSize = state.stackSize := by
  unfold gc at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (simp only [reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp)

end Flapjack.WordSemStateFiniteExact
