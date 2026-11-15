module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.HoleRelation
public import Flapjack.Compiler.Backend.BviTmc.Proofs.WellFormed
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Environments and allocated holes for call-block simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockEnvironment
open BviTmc BvlSem

theorem holFmapAsFiniteSupportParamWitness_allocHoleHasVal_f {α : Type} (f : HolFiniteMapExact α Nat) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by cases f; exact ⟨fun _ => rfl, rfl, rfl⟩
theorem holFmapAsFiniteSupportParamWitness_allocHoleHasVal_refs {β : Type} (refs : HolFiniteMapExact Nat (Ref β)) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).lookup key = refs.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).finiteSupport = refs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs) = refs := by cases refs; exact ⟨fun _ => rfl, rfl, rfl⟩

/-- An extra environment slot identifies a fresh, unfinalised allocated hole. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "alloc_hole_has_val_def"
  (fmap_as_finite_support_parameters := [f, refs])]
noncomputable def allocHoleHasVal {α β : Type} (f : HolFiniteMapExact α Nat)
    (refs : HolFiniteMapExact Nat (Ref β)) (extras : List Value) (ptrIndex childIndex : Nat) (c : β) : Prop :=
  ∃ holePtr tag left right, ptrIndex < extras.length ∧
    holEl ptrIndex extras = .refPtr false holePtr ∧ childIndex = left.length ∧
    BackendCommon.smallEnoughInt (Int.ofNat left.length) ∧ holePtr ∉ mapRange f ∧
    refs.lookup holePtr = some (.mutBlock tag false left c right)

theorem holFmapAsFiniteSupportParamWitness_wfVars_list_rel_f (f : HolFiniteMapExact Nat Nat) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by cases f; exact ⟨fun _ => rfl, rfl, rfl⟩

/-- Well-formed variable selections yield pointwise related values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "wf_vars_list_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem wfVars_list_rel (vars : List Nat) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (env1 env2 : List Value) (h : envRel opt f env1 env2 ∧ wfVars env1.length vars) :
    List.Forall₂ (valueRel f) (vars.map (fun n => holEl n env1)) (vars.map (fun n => holEl n env2)) := by
  obtain ⟨related, wf⟩ := h
  induction vars with
  | nil => exact .nil
  | cons n rest ih =>
    apply List.Forall₂.cons
    · exact envRel_el opt f env1 env2 n ⟨related, wf n (by simp)⟩
    · apply ih
      intro k member
      exact wf k (by simp [member])

theorem holFmapAsFiniteSupportParamWitness_wfVars_env_rel_f (f : HolFiniteMapExact Nat Nat) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by cases f; exact ⟨fun _ => rfl, rfl, rfl⟩

/-- Selecting well-formed variables produces related unoptimized environments. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "wf_vars_env_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem wfVars_env_rel (vars : List Nat) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (env1 env2 : List Value) (h : envRel opt f env1 env2 ∧ wfVars env1.length vars) :
    envRel false f (vars.map (fun n => holEl n env1)) (vars.map (fun n => holEl n env2)) := by
  exact ⟨_, [], by simp, wfVars_list_rel vars opt f env1 env2 h, by simp⟩

theorem holFmapAsFiniteSupportParamWitness_wfVars_env_rel_opt_f (f : HolFiniteMapExact Nat Nat) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by cases f; exact ⟨fun _ => rfl, rfl, rfl⟩

/-- Selecting well-formed variables and appending hole metadata produces a
related optimized environment. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "wf_vars_env_rel_opt"
  (fmap_as_finite_support_parameters := [f])]
theorem wfVars_env_rel_opt (vars : List Nat) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (env1 env2 : List Value) (ptr : Nat) (idx : Int)
    (h : envRel opt f env1 env2 ∧ wfVars env1.length vars ∧ BackendCommon.smallEnoughInt idx) :
    envRel true f (vars.map (fun n => holEl n env1))
      (vars.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number idx]) := by
  obtain ⟨related, wf, small⟩ := h
  refine ⟨_, [.refPtr false ptr, .number idx], rfl, wfVars_list_rel vars opt f env1 env2 ⟨related, wf⟩, ?_⟩
  intro _
  exact ⟨rfl, ptr, idx, rfl, rfl, small⟩

theorem holFmapAsFiniteSupportParamWitness_stateRefRel_sub_f (f : HolFiniteMapExact Nat Nat) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by cases f; exact ⟨fun _ => rfl, rfl, rfl⟩
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_sub_source (source : HolFiniteMapExact Nat (Ref Value)) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad source)).lookup key = source.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad source)).finiteSupport = source.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad source) = source := by cases source; exact ⟨fun _ => rfl, rfl, rfl⟩
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_sub_target (target : HolFiniteMapExact Nat (Ref Value)) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad target)).lookup key = target.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad target)).finiteSupport = target.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad target) = target := by cases target; exact ⟨fun _ => rfl, rfl, rfl⟩

/-- Removing a target reference outside the pointer-map range preserves the
state-reference relation.

Intended HOL counterpart, pending statement and finite-map carrier source review.
Former reference: @[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_ref_rel_sub" (fmap_as_finite_support_parameters := [f, source, target])] -/
theorem stateRefRel_sub (ptr : Nat) (f : HolFiniteMapExact Nat Nat)
    (source : HolFiniteMapExact Nat (Ref Value)) (target : HolFiniteMapExact Nat (Ref Value))
    (outside : ptr ∉ mapRange f) (related : stateRefRel f source target) :
    stateRefRel f source (target.eraseEq ptr) := by
  refine ⟨related.1, ?_⟩
  intro i v found
  obtain ⟨j, w, mapped, cells, lookup⟩ := related.2 i v found
  have different : j ≠ ptr := by
    intro equal
    subst j
    exact outside ⟨i, mapped⟩
  exact ⟨j, w, mapped, cells, by simpa [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, different] using lookup⟩

end Flapjack.Compiler.Backend.BviTmc.CallBlockEnvironment
