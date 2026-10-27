import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRel

/-! Source-to-flat store and state relations. These use the factored value
relation, whose full correspondence to the original HOL relation remains open. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL

/-- Flapjack infrastructure relating source and flat store entries. This is
untagged until the underlying value relation is reviewed against HOL. -/
inductive StoreValueRel (genv : GlobalEnv) : StoreValue SemanticPrimitivesHOL.Value →
    StoreValue FlatSem.Value → Prop where
  | refv {v v'} (related : ValueRel genv v v') : StoreValueRel genv (.refv v) (.refv v')
  | w8array (bytes) : StoreValueRel genv (.w8array bytes) (.w8array bytes)
  | varray {vs vs'} (related : List.Forall₂ (ValueRel genv) vs vs') :
      StoreValueRel genv (.varray vs) (.varray vs')
  | thunk (mode) {v v'} (related : ValueRel genv v v') :
      StoreValueRel genv (.thunk mode v) (.thunk mode v')

/-- Flapjack infrastructure relating evaluator states. The flat store has the
original reserved leading entry; no relationship is imposed on that entry.
This is untagged until the underlying value relation is reviewed against HOL. -/
inductive StateRel {C F : Type} (genv : GlobalEnv) :
    SemanticPrimitivesHOL.State F → FlatSem.State C F → Prop where
  | intro (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
      (nonempty : flat.refs ≠ [])
      (refs : List.Forall₂ (StoreValueRel genv) source.refs flat.refs.tail)
      (clock : source.clock = flat.clock)
      (ffi : source.ffi = flat.ffi) : StateRel genv source flat

/-- Flapjack list infrastructure: a pointwise relation preserves successful
indexed lookup. -/
theorem forall₂_lookup {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) (n : Nat) (x : α) (lookup : xs[n]? = some x) :
    ∃ y, ys[n]? = some y ∧ R x y := by
  induction related generalizing n with
  | nil => simp at lookup
  | @cons a b xs ys head tail ih =>
    cases n with
    | zero =>
      simp at lookup
      subst x
      exact ⟨b, rfl, head⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at lookup ⊢
      exact ih n lookup

/-- A source reference lookup has a related flat reference one slot later.
This is infrastructure over the factored source-to-flat value relation. -/
theorem stateRel_ref_lookup {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (related : StateRel genv source flat) (n : Nat) (value : SemanticPrimitivesHOL.Value)
    (lookup : storeLookup n source.refs = some (.refv value)) :
    ∃ value', storeLookup (n + 1) flat.refs = some (.refv value') ∧ ValueRel genv value value' := by
  cases related with
  | intro nonempty refs _ _ =>
    obtain ⟨entry, rest, hflat⟩ := List.exists_cons_of_ne_nil nonempty
    have relatedRest : List.Forall₂ (StoreValueRel genv) source.refs rest := by simpa [hflat] using refs
    obtain ⟨found, hfound, hrel⟩ := forall₂_lookup relatedRest n (.refv value) lookup
    cases hrel with
    | refv hvalue =>
      refine ⟨_, ?_, hvalue⟩
      simpa [storeLookup, hflat, Nat.add_comm] using hfound

end Flapjack.Compiler.Backend.SourceToFlat
