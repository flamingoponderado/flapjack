import Flapjack.Compiler.Backend.Semantics.WordSem.Env

namespace Flapjack.WordSemJumpExcConstSupport

/-- Canonical roundtrip for the actual native exception-jump state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end Flapjack.WordSemJumpExcConstSupport

namespace Flapjack.WordSemStateFiniteExact

/-- Complete original jump_exc_const contract (wordProps943-963): all
fourteen preserved fields and the sole successful exception-jump premise,
with arbitrary source/post states and returned label pair. No handler-validity
or frame-shape premise is added. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "jump_exc_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem jumpExcConst {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F) (label : Nat × Nat)
    (h : jumpExc state = some (next, label)) :
    next.be = state.be ∧
    next.gcFun = state.gcFun ∧
    next.mdomain = state.mdomain ∧
    next.shMdomain = state.shMdomain ∧
    next.code = state.code ∧
    next.codeBuffer = state.codeBuffer ∧
    next.dataBuffer = state.dataBuffer ∧
    next.compile = state.compile ∧
    next.compileOracle = state.compileOracle ∧
    next.clock = state.clock ∧
    next.ffi = state.ffi ∧
    next.stackLimit = state.stackLimit ∧
    next.stackMax = state.stackMax ∧
    next.stackSize = state.stackSize := by
  unfold jumpExc at h
  repeat' split at h
  all_goals first
    | (simp only [reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       rcases h with ⟨h, _⟩
       subst h
       simp)

end Flapjack.WordSemStateFiniteExact
