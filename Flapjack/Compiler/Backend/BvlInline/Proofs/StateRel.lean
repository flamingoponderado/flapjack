module

public import Flapjack.Compiler.Backend.BvlInline.RemoveTicks
public import Flapjack.Compiler.Backend.Semantics.BvlSem.State
public import Flapjack.Misc.Sptree.Map
public import Flapjack.HolRef

@[expose] public section

/-! State relation for the tick-removal part of BVL inlining correctness. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

namespace InlineStateCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineStateCarrier

/-- Relate pre- and post-removal states, including compiler callbacks and
every future oracle entry. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "state_rel_def" 15
  (fmap_as_finite_support := [refs])]
def stateRel {C F : Type} (s t : Flapjack.Compiler.Backend.BvlSem.State C F) : Prop :=
  t = { s with
    code := sptMap (fun (arity, body) => (arity, removeTicksSing body)) s.code
    compile := t.compile
    compileOracle := fun n => ((s.compileOracle n).1,
      (s.compileOracle n).2.map fun (name, arity, body) => (name, arity, removeTicksSing body)) } ∧
  s.compile = fun config program =>
    t.compile config (program.map fun (name, arity, body) => (name, arity, removeTicksSing body))

/-- The relation leaves the runtime data and FFI state unchanged. This is
Flapjack proof infrastructure obtained by projecting the source relation. -/
theorem stateRel_fields {C F : Type} (s t : State C F) (related : stateRel s t) :
    t.globals = s.globals ∧ t.refs = s.refs ∧ t.clock = s.clock ∧ t.ffi = s.ffi := by
  obtain ⟨fields, _⟩ := related
  constructor
  · simpa using congrArg (fun state : State C F => state.globals) fields
  constructor
  · simpa using congrArg (fun state : State C F => state.refs) fields
  constructor
  · simpa using congrArg (fun state : State C F => state.clock) fields
  · simpa using congrArg (fun state : State C F => state.ffi) fields

end Flapjack.Compiler.Backend.BvlInline.Proofs
