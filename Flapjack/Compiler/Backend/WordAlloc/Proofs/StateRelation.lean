import Flapjack.Compiler.Backend.Semantics.WordSem.State

namespace Flapjack.WordAlloc

namespace StateRelationWitnesses

/-- Canonical imported WordSem carrier roundtrip for this relation's map fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StateRelationWitnesses

/-- Exact HOL word_state_eq_rel: equality of all 21 listed fields, in source
order. Locals and permutation are deliberately absent; localsSize is present.
This relation does not assert the allocation simulation itself. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def wordStateEqRel {width : Nat} [NeZero width] {C F : Type}
    (s t : WordSemStateFiniteExact width C F) : Prop :=
  t.fpRegs = s.fpRegs ∧
  t.store = s.store ∧
  t.localsSize = s.localsSize ∧
  t.stack = s.stack ∧
  t.stackLimit = s.stackLimit ∧
  t.stackMax = s.stackMax ∧
  t.stackSize = s.stackSize ∧
  t.memory = s.memory ∧
  t.mdomain = s.mdomain ∧
  t.shMdomain = s.shMdomain ∧
  t.gcFun = s.gcFun ∧
  t.handler = s.handler ∧
  t.clock = s.clock ∧
  t.code = s.code ∧
  t.ffi = s.ffi ∧
  t.be = s.be ∧
  t.termdep = s.termdep ∧
  t.compile = s.compile ∧
  t.compileOracle = s.compileOracle ∧
  t.codeBuffer = s.codeBuffer ∧
  t.dataBuffer = s.dataBuffer

end Flapjack.WordAlloc
