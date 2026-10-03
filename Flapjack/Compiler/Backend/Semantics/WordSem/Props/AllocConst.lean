import Flapjack.Compiler.Backend.Semantics.WordSem.Props.GcConst
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PopEnvConst

namespace Flapjack.WordSemAllocConstSupport

/-- Canonical roundtrip for the actual native allocation-state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end Flapjack.WordSemAllocConstSupport

namespace Flapjack.WordSemStateFiniteExact

/-- Complete original alloc_const contract (wordProps649-666). All ten
original field conclusions follow from the sole allocation equation, covering
GC/error/space-success/NotEnoughSpace branches with arbitrary callback/state.
No successful-allocation or resource-safety premise is supplied. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "alloc_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocConst {width : Nat} [NeZero width] {C F : Type}
    (amount : BitVec width) (names : WordLangCutsetsHOL)
    (state next : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (h : alloc amount names state = (result, next)) :
    next.clock = state.clock ∧
    next.ffi = state.ffi ∧
    next.code = state.code ∧
    next.be = state.be ∧
    next.codeBuffer = state.codeBuffer ∧
    next.dataBuffer = state.dataBuffer ∧
    next.compile = state.compile ∧
    next.compileOracle = state.compileOracle ∧
    next.stackLimit = state.stackLimit ∧
    next.stackSize = state.stackSize := by
  unfold alloc at h
  split at h
  · cases h; simp [flushState]
  · rename_i envs _
    split at h
    · cases h; simp [flushState]
    · rename_i collected hg
      have gcFields := gcConst _ _ hg
      simp only [pushEnv, setStore] at gcFields
      rcases gcFields with ⟨gcClock, gcFfi, gcCode, gcBe, gcCodeBuffer,
        gcDataBuffer, gcCompile, _, gcOracle, _, gcLimit, _, gcSize⟩
      split at h
      · cases h
        exact ⟨gcClock, gcFfi, gcCode, gcBe, gcCodeBuffer,
          gcDataBuffer, gcCompile, gcOracle, gcLimit, gcSize⟩
      · rename_i popped hp
        rcases popEnvConst _ _ hp with ⟨popClock, popFfi, popBe, popCompile,
          popOracle, _, _, _, _, _, _, _, _, popDataBuffer, popCodeBuffer,
          popCode, popLimit, _, popSize⟩
        have fields : popped.clock = state.clock ∧ popped.ffi = state.ffi ∧
            popped.code = state.code ∧ popped.be = state.be ∧
            popped.codeBuffer = state.codeBuffer ∧ popped.dataBuffer = state.dataBuffer ∧
            popped.compile = state.compile ∧ popped.compileOracle = state.compileOracle ∧
            popped.stackLimit = state.stackLimit ∧ popped.stackSize = state.stackSize :=
          ⟨popClock.trans gcClock, popFfi.trans gcFfi, popCode.trans gcCode,
            popBe.trans gcBe, popCodeBuffer.trans gcCodeBuffer,
            popDataBuffer.trans gcDataBuffer, popCompile.trans gcCompile,
            popOracle.trans gcOracle, popLimit.trans gcLimit, popSize.trans gcSize⟩
        split at h
        · cases h; exact fields
        · split at h
          · cases h; exact fields
          · cases h; exact fields
          · cases h; exact fields

end Flapjack.WordSemStateFiniteExact
