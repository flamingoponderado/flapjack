import Flapjack.Compiler.Backend.Semantics.WordSem.Env

namespace Flapjack.WordSemPopEnvConstSupport

/-- Canonical roundtrip for the actual native environment-state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end Flapjack.WordSemPopEnvConstSupport

namespace Flapjack.WordSemStateFiniteExact

/-- Complete original pop_env_const contract (wordProps475-497). The sole
successful-pop premise covers arbitrary stacks and both handler branches;
all nineteen original preserved fields are stated in original order. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "pop_env_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem popEnvConst {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F)
    (h : popEnv state = some next) :
    next.clock = state.clock ∧
    next.ffi = state.ffi ∧
    next.be = state.be ∧
    next.compile = state.compile ∧
    next.compileOracle = state.compileOracle ∧
    next.memory = state.memory ∧
    next.mdomain = state.mdomain ∧
    next.shMdomain = state.shMdomain ∧
    next.store = state.store ∧
    next.fpRegs = state.fpRegs ∧
    next.gcFun = state.gcFun ∧
    next.termdep = state.termdep ∧
    next.permute = state.permute ∧
    next.dataBuffer = state.dataBuffer ∧
    next.codeBuffer = state.codeBuffer ∧
    next.code = state.code ∧
    next.stackLimit = state.stackLimit ∧
    next.stackMax = state.stackMax ∧
    next.stackSize = state.stackSize := by
  unfold popEnv at h
  repeat' split at h
  all_goals first
    | (simp only [reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp)

end Flapjack.WordSemStateFiniteExact
