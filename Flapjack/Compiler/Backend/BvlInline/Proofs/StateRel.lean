import Flapjack.Compiler.Backend.BvlInline.RemoveTicks
import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Flapjack.Misc.Sptree.Map
import Flapjack.HolRef

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

/-- Code lookup commutes with tick removal under the relation. -/
theorem stateRel_lookup {C F : Type} (s t : State C F) (related : stateRel s t) (name : Nat) :
    sptLookup name t.code = (sptLookup name s.code).map
      (fun (arity, body) => (arity, removeTicksSing body)) := by
  have fields := congrArg (fun state : State C F => sptLookup name state.code) related.1
  simpa [sptLookup_sptMap] using fields

/-- Each oracle program is transformed while its configuration is retained. -/
theorem stateRel_oracle {C F : Type} (s t : State C F) (related : stateRel s t) (n : Nat) :
    t.compileOracle n = ((s.compileOracle n).1,
      (s.compileOracle n).2.map fun (name, arity, body) => (name, arity, removeTicksSing body)) := by
  exact congrArg (fun state : State C F => state.compileOracle n) related.1

/-- Related compiler callbacks agree after transforming their program input. -/
theorem stateRel_compile {C F : Type} (s t : State C F) (related : stateRel s t)
    (config : C) (program : List (Nat × Nat × Bvl.Exp)) :
    s.compile config program = t.compile config
      (program.map fun (name, arity, body) => (name, arity, removeTicksSing body)) := by
  exact congrFun (congrFun related.2 config) program

end Flapjack.Compiler.Backend.BvlInline.Proofs
