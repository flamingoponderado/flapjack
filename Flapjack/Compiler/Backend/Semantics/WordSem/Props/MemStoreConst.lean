import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

namespace Flapjack.WordSemMemStoreConstSupport

/-- Canonical roundtrip for the actual native memory-store state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end Flapjack.WordSemMemStoreConstSupport

namespace Flapjack.WordSemStateFiniteExact

/-- Complete original mem_store_const contract (wordProps794-815): all
eighteen original conclusions, arbitrary address/value/states, and only the
successful-store premise. No extra alignment, domain or safety restriction. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "mem_store_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memStoreConst {width : Nat} [NeZero width] {C F : Type}
    (address : BitVec width) (value : WordLocW width)
    (state next : WordSemStateFiniteExact width C F)
    (h : memStore address value state = some next) :
    next.locals = state.locals ∧
    next.clock = state.clock ∧
    next.be = state.be ∧
    next.gcFun = state.gcFun ∧
    next.mdomain = state.mdomain ∧
    next.shMdomain = state.shMdomain ∧
    next.ffi = state.ffi ∧
    next.handler = state.handler ∧
    next.code = state.code ∧
    next.codeBuffer = state.codeBuffer ∧
    next.dataBuffer = state.dataBuffer ∧
    next.compile = state.compile ∧
    next.compileOracle = state.compileOracle ∧
    next.stack = state.stack ∧
    next.localsSize = state.localsSize ∧
    next.stackLimit = state.stackLimit ∧
    next.stackMax = state.stackMax ∧
    next.stackSize = state.stackSize := by
  unfold memStore at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp
  · simp only [reduceCtorEq] at h

end Flapjack.WordSemStateFiniteExact
