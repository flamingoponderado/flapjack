import Flapjack.Compiler.Backend.BviTmc.Proofs.HeapRelation
import Flapjack.Compiler.Backend.Semantics.BvlSem.Thunk
import Flapjack.Compiler.Backend.Semantics.BviSem.Thunk
import Flapjack.Compiler.Backend.BviTmc.Proofs.StateRelation

/-! Thunk inspection under the TMC heap relation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem

private def maptoBroadlookup {α β : Type} (f : HolFiniteMapExact α β) : α → Option β := f.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_destThunk_notThunk_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_destThunk_notThunk_rel_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_destThunk_notThunk_rel_target (target : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup target) target.finiteSupport = target := by cases target; rfl

/-- A value that is not a thunk remains so under pointer renaming. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "dest_thunk_not_thunk_rel"
  (fmap_as_finite_support_parameters := [refs, target, f])]
theorem destThunk_notThunk_rel (v v' : Value) (refs : HolFiniteMapExact Nat (Ref Value))
    (target : HolFiniteMapExact Nat (Ref Value)) (f : HolFiniteMapExact Nat Nat)
    (notThunk : BvlSem.destThunk v refs = .notThunk) (values : valueRel f v v')
    (heaps : stateRefRel f refs target) : BvlSem.destThunk v' target = .notThunk := by
  cases values with
  | number i => rfl
  | word64 word => rfl
  | block tag xs ys related => rfl
  | codePtr n => rfl
  | refPtr n m flag mapped =>
    obtain ⟨_, _, sourceFound, targetFound, cells⟩ := stateRefRel_lookup f n m refs target mapped heaps
    cases cells with
    | byteArray b bytes => simp [BvlSem.destThunk, targetFound]
    | valueArray xs ys related => simp [BvlSem.destThunk, targetFound]
    | thunk mode x y related =>
      cases flag <;> simp [BvlSem.destThunk, sourceFound] at notThunk

/-- Flapjack helper: a permitted thunk update stays permitted for the
related value and target heap. -/
theorem goodThunkUpdate_rel (mode : AstHOL.ThunkMode) (v v' : Value)
    (refs : HolFiniteMapExact Nat (Ref Value)) (target : HolFiniteMapExact Nat (Ref Value))
    (f : HolFiniteMapExact Nat Nat) (good : ¬BvlSem.badThunkUpdate mode v refs)
    (values : valueRel f v v') (heaps : stateRefRel f refs target) :
    ¬BvlSem.badThunkUpdate mode v' target := by
  intro bad
  apply good
  refine ⟨bad.1, ?_⟩
  intro notThunk
  exact bad.2 (destThunk_notThunk_rel v v' refs target f notThunk values heaps)

theorem holFmapAsFiniteSupportParamWitness_destThunkRetRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Related thunk observations agree on errors and modes and relate the
payload values returned by thunk inspection. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "dest_thunk_ret_rel_def"
  (fmap_as_finite_support_parameters := [f])]
def destThunkRetRel (f : HolFiniteMapExact Nat Nat) (a b : BviSem.DestThunkResult) : Prop :=
  (a = .badRef ∧ b = .badRef) ∨ (a = .notThunk ∧ b = .notThunk) ∨
    ∃ mode mode' v v', a = .isThunk mode v ∧ b = .isThunk mode' v' ∧ mode = mode' ∧ valueRel f v v'

namespace ThunkWitness
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ThunkWitness

/-- Thunk observations at related environment entries are related. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "dest_thunk_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
theorem destThunk_rel {C F : Type} (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (env1 env2 : List Value) (source : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (index : Nat) (env : envRel opt f env1 env2) (states : stateRel f source target)
    (bound : index < env1.length) :
    destThunkRetRel f (BviSem.destThunk (holEl index env1) source.refs)
      (BviSem.destThunk (holEl index env2) target.refs) := by
  have related := envRel_el opt f env1 env2 index env bound
  generalize sourceValue : holEl index env1 = v at related ⊢
  generalize targetValue : holEl index env2 = w at related ⊢
  cases related with
  | number i => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | word64 word => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | block tag xs ys fields => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | codePtr n => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | refPtr n m flag mapped =>
    obtain ⟨_, _, sourceFound, targetFound, cells⟩ := stateRefRel_lookup f n m source.refs target.refs mapped states.1
    cases cells with
    | byteArray b bytes => simp [destThunkRetRel, BviSem.destThunk, sourceFound, targetFound]
    | valueArray xs ys fields => simp [destThunkRetRel, BviSem.destThunk, sourceFound, targetFound]
    | thunk mode x y payload =>
      cases flag with
      | true => simp [destThunkRetRel, BviSem.destThunk, sourceFound, targetFound]
      | false =>
        right
        right
        exact ⟨mode, mode, x, y, by simp [BviSem.destThunk, sourceFound],
          by simp [BviSem.destThunk, targetFound], rfl, payload⟩

end Flapjack.Compiler.Backend.BviTmc
