import Flapjack.Compiler.Backend.FlatElim.Proofs.ValueGlobals

/-! State relation used by the flat dead-code elimination proof. -/
namespace Flapjack.Compiler.Backend.FlatElim

/-- Relate the original global list to the list after unreachable entries are
removed, retaining every reachable value and its closed dependency set. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "globals_rel_def"]
def globalsRel (reachable : NumSet) (source target : List (Option FlatSem.Value)) : Prop :=
  source.length = target.length ∧
  (∀ n, sptMem n reachable → n < target.length → source[n]?.getD none = target[n]?.getD none) ∧
  (∀ n value, n < target.length → target[n]?.getD none = some value → source[n]?.getD none = some value) ∧
  (∀ n, n < target.length → source[n]?.getD none = none → target[n]?.getD none = none) ∧
  (∀ n value, sptMem n reachable → n < target.length → target[n]?.getD none = some value →
    valueHasEval value = false ∧ ∀ key, sptMem key (findValueGlobals value) → sptMem key reachable)

/-- Global removal relations compose without changing the reachable set. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "globals_rel_trans"]
theorem globalsRel_trans (reachable : NumSet) (first middle last : List (Option FlatSem.Value))
    (relations : globalsRel reachable first middle ∧ globalsRel reachable middle last) :
    globalsRel reachable first last := by
  obtain ⟨⟨length1, reach1, present1, empty1, _⟩, ⟨length2, reach2, present2, empty2, closed⟩⟩ := relations
  refine ⟨length1.trans length2, ?_, ?_, ?_, closed⟩
  · intro n inReachable bound
    exact (reach1 n inReachable (by omega)).trans (reach2 n inReachable bound)
  · intro n value bound present
    exact present1 n value (by omega) (present2 n value bound present)
  · intro n bound empty
    exact empty2 n bound (empty1 n (by omega) empty)

/-- Stores contain no dynamic Eval values, including in reference and thunk
payloads. This helper expands the original store-value list traversal. -/
def storeHasNoEval (refs : List (Flapjack.SemanticPrimitivesHOL.StoreValue FlatSem.Value)) : Prop :=
  ∀ ref ∈ refs, match ref with
    | .refv value | .thunk _ value => valueHasEval value = false
    | .varray values => ∀ value ∈ values, valueHasEval value = false
    | .w8array _ => True

/-- The original flat state relation, including all reference dependencies
and the absence of Eval in stored values. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_state_rel_def"]
def flatStateRel {C F : Type} (reachable : NumSet) (source target : FlatSem.State C F) : Prop :=
  source.clock = target.clock ∧ source.refs = target.refs ∧ source.ffi = target.ffi ∧
  globalsRel reachable source.globals target.globals ∧
  (∀ key, sptMem key (findRefsGlobals source.refs) → sptMem key reachable) ∧
  storeHasNoEval source.refs

/-- The flat state relation composes for a fixed reachable set. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_state_rel_trans"]
theorem flatStateRel_trans {C F : Type} (reachable : NumSet) (first middle last : FlatSem.State C F)
    (relations : flatStateRel reachable first middle ∧ flatStateRel reachable middle last) :
    flatStateRel reachable first last := by
  obtain ⟨⟨clock1, refs1, ffi1, globals1, refsGlobals, noEval⟩,
    ⟨clock2, refs2, ffi2, globals2, _, _⟩⟩ := relations
  exact ⟨clock1.trans clock2, refs1.trans refs2, ffi1.trans ffi2,
    globalsRel_trans reachable first.globals middle.globals last.globals ⟨globals1, globals2⟩,
    refsGlobals, noEval⟩

end Flapjack.Compiler.Backend.FlatElim
