import Flapjack.Compiler.Backend.BviTmc.Proofs.HeapRelation
import Flapjack.Compiler.Backend.Semantics.BvlSem.Build

/-! Mutable-hole invariants used by the TMC evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem

private def maptoBroadlookup {α β : Type} (f : HolFiniteMapExact α β) : α → Option β := f.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

/-- HOL finite-map range, as a membership predicate. -/
def mapRange {α β : Type} (f : HolFiniteMapExact α β) : Set β :=
  {value | ∃ key, f.lookup key = some value}

theorem holFmapAsFiniteSupportParamWitness_holeHasVal_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holeHasVal_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- The optimized environment identifies a mutable block containing the
current value in its hole. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "hole_has_val_def"
  (fmap_as_finite_support_parameters := [f, refs])]
noncomputable def holeHasVal (f : HolFiniteMapExact Nat Nat) (env1 env2 : List Value)
    (refs : HolFiniteMapExact Nat (Ref Value)) (c : Value) : Prop :=
  env2.length = env1.length + 2 ∧
  ∃ ptr tag finalised left right,
    holEl env1.length env2 = .refPtr false ptr ∧
    holEl (env1.length + 1) env2 = .number (Int.ofNat left.length) ∧
    BackendCommon.smallEnoughInt (Int.ofNat left.length) ∧ ptr ∉ mapRange f ∧
    refs.lookup ptr = some (.mutBlock tag finalised left c right)

theorem holFmapAsFiniteSupportParamWitness_holesUnchangedExcept_f {α β : Type}
    (f : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchangedExcept_refs {β γ : Type}
    (refs : HolFiniteMapExact β (Ref γ)) : mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchangedExcept_refsNew {β γ : Type}
    (refsNew : HolFiniteMapExact β (Ref γ)) : mapofBroad (maptoBroadlookup refsNew) refsNew.finiteSupport = refsNew := by cases refsNew; rfl

/-- Existing mutable blocks outside the original pointer-map range keep
their tag and surrounding values; listed holes may change their child. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_unchanged_except_def"
  (fmap_as_finite_support_parameters := [f, refs, refsNew])]
def holesUnchangedExcept {α β γ : Type} (f : HolFiniteMapExact α β)
    (refs : HolFiniteMapExact β (Ref γ)) (refsNew : HolFiniteMapExact β (Ref γ)) (changed : Set β) : Prop :=
  ∀ ptr tag finalised left child right, ptr ∉ mapRange f →
    refs.lookup ptr = some (.mutBlock tag finalised left child right) →
    ∃ finalised' child', refsNew.lookup ptr = some (.mutBlock tag finalised' left child' right) ∧
      (ptr ∉ changed → child = child')

theorem holFmapAsFiniteSupportParamWitness_holeNotFinalised_refs {β γ : Type}
    (refs : HolFiniteMapExact β (Ref γ)) : mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- A location holds a mutable block that is not yet finalised. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "hole_not_finalised_def"
  (fmap_as_finite_support_parameters := [refs])]
def holeNotFinalised {β γ : Type} (refs : HolFiniteMapExact β (Ref γ)) (ptr : β) : Prop :=
  ∃ tag left child right, refs.lookup ptr = some (.mutBlock tag false left child right)

theorem holFmapAsFiniteSupportParamWitness_holesStillNotFinalised_f {α β : Type}
    (f : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStillNotFinalised_refs {β γ : Type}
    (refs : HolFiniteMapExact β (Ref γ)) : mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStillNotFinalised_refsNew {β γ : Type}
    (refsNew : HolFiniteMapExact β (Ref γ)) : mapofBroad (maptoBroadlookup refsNew) refsNew.finiteSupport = refsNew := by cases refsNew; rfl

/-- Every unfinalised hole outside the pointer-map range remains unfinalised. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_still_not_finalised_def"
  (fmap_as_finite_support_parameters := [f, refs, refsNew])]
def holesStillNotFinalised {α β γ : Type} (f : HolFiniteMapExact α β)
    (refs : HolFiniteMapExact β (Ref γ)) (refsNew : HolFiniteMapExact β (Ref γ)) : Prop :=
  ∀ ptr, ptr ∉ mapRange f → holeNotFinalised refs ptr → holeNotFinalised refsNew ptr

theorem holFmapAsFiniteSupportParamWitness_onlyFresh_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_onlyFresh_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl
theorem holFmapAsFiniteSupportParamWitness_onlyFresh_refsOld (refsOld : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refsOld) refsOld.finiteSupport = refsOld := by cases refsOld; rfl

/-- Newly introduced pointer-map targets are absent from the old heap. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "only_fresh_def"
  (fmap_as_finite_support_parameters := [f, g, refsOld])]
def onlyFresh (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat)
    (refsOld : HolFiniteMapExact Nat (Ref Value)) : Prop :=
  ∀ n, n ∈ mapRange g ∧ n ∉ mapRange f → n ∉ refsOld.domain

theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_refl_f {α β : Type} (f : HolFiniteMapExact α β) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_refl_refs {β γ : Type} (refs : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- A heap trivially preserves its own mutable holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_unchanged_except_refl"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem holesUnchanged_refl {α β γ : Type} (f : HolFiniteMapExact α β)
    (refs : HolFiniteMapExact β (Ref γ)) (changed : Set β) : holesUnchangedExcept f refs refs changed := by
  intro ptr tag finalised left child right _ found
  exact ⟨finalised, child, found, fun _ => rfl⟩

theorem holFmapAsFiniteSupportParamWitness_holesStill_refl_f {α β : Type} (f : HolFiniteMapExact α β) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_refl_refs {β γ : Type} (refs : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- A heap trivially preserves its own unfinalised holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_still_not_finalised_refl"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem holesStill_refl {α β γ : Type} (f : HolFiniteMapExact α β)
    (refs : HolFiniteMapExact β (Ref γ)) : holesStillNotFinalised f refs refs := by
  intro _ _ found
  exact found

theorem holFmapAsFiniteSupportParamWitness_onlyFresh_refl_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_onlyFresh_refl_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- A pointer map adds no targets relative to itself. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "only_fresh_refl"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem onlyFresh_refl (f : HolFiniteMapExact Nat Nat) (refs : HolFiniteMapExact Nat (Ref Value)) :
    onlyFresh f f refs := by
  intro _ ⟨member, absent⟩
  exact (absent member).elim

theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_subset_f {α β : Type} (f : HolFiniteMapExact α β) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_subset_refs {β γ : Type} (refs : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_subset_refsNew {β γ : Type} (refsNew : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup refsNew) refsNew.finiteSupport = refsNew := by cases refsNew; rfl

/-- Allowing changes at more locations preserves the hole invariant. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_unchanged_except_subset"
  (fmap_as_finite_support_parameters := [f, refs, refsNew])]
theorem holesUnchanged_subset {α β γ : Type} (f : HolFiniteMapExact α β)
    (refs : HolFiniteMapExact β (Ref γ)) (refsNew : HolFiniteMapExact β (Ref γ))
    (changed larger : Set β) (related : holesUnchangedExcept f refs refsNew changed)
    (subset : changed ⊆ larger) : holesUnchangedExcept f refs refsNew larger := by
  intro ptr tag finalised left child right outside found
  obtain ⟨finalised', child', lookup, same⟩ := related ptr tag finalised left child right outside found
  exact ⟨finalised', child', lookup, fun absent => same (fun mem => absent (subset mem))⟩

theorem holFmapAsFiniteSupportParamWitness_nonFresh_not_in_range_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_nonFresh_not_in_range_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl
theorem holFmapAsFiniteSupportParamWitness_nonFresh_not_in_range_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- A previously allocated non-pointer-map location cannot become a new
pointer-map target under the freshness relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "non_fresh_not_in_frange"
  (fmap_as_finite_support_parameters := [f, g, refs])]
theorem nonFresh_not_in_range (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (ptr : Nat) (allocated : ptr ∈ refs.domain)
    (outside : ptr ∉ mapRange f) (fresh : onlyFresh f g refs) : ptr ∉ mapRange g := by
  intro member
  exact fresh ptr ⟨member, outside⟩ allocated

theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_trans_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_trans_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_trans_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_trans_middle (middle : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup middle) middle.finiteSupport = middle := by cases middle; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_trans_final (final : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup final) final.finiteSupport = final := by cases final; rfl

/-- Hole preservation composes as the pointer map grows only into fresh
heap locations. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_unchanged_except_trans"
  (fmap_as_finite_support_parameters := [f, g, refs, middle, final])]
theorem holesUnchanged_trans (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (middle : HolFiniteMapExact Nat (Ref Value))
    (final : HolFiniteMapExact Nat (Ref Value)) (changed : Set Nat)
    (first : holesUnchangedExcept f refs middle changed) (second : holesUnchangedExcept g middle final changed)
    (fresh : onlyFresh f g refs) (_submap : finiteSubmap f g) : holesUnchangedExcept f refs final changed := by
  intro ptr tag finalised left child right outside found
  obtain ⟨middleFinalised, middleChild, middleFound, same1⟩ := first ptr tag finalised left child right outside found
  have allocated : ptr ∈ refs.domain := by simp [HolFiniteMapExact.domain, found]
  have outsideNew := nonFresh_not_in_range f g refs ptr allocated outside fresh
  obtain ⟨finalFinalised, finalChild, finalFound, same2⟩ :=
    second ptr tag middleFinalised left middleChild right outsideNew middleFound
  exact ⟨finalFinalised, finalChild, finalFound, fun unchanged => (same1 unchanged).trans (same2 unchanged)⟩

theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_rangeUpdate_f {α β : Type}
    (f : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_rangeUpdate_refs {β γ : Type}
    (refs : HolFiniteMapExact β (Ref γ)) : mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- Updating a mapped location cannot change a mutable hole outside the map range. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_unchanged_except_frange_update"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem holesUnchanged_rangeUpdate {α β γ : Type} [DecidableEq β] (f : HolFiniteMapExact α β)
    (p : α) (key : β) (value : Ref γ) (refs : HolFiniteMapExact β (Ref γ))
    (mapped : f.lookup p = some key) : holesUnchangedExcept f refs (refs.updateEq (key, value)) ∅ := by
  intro ptr tag finalised left child right outside found
  have different : ptr ≠ key := by
    intro equal
    subst ptr
    exact outside ⟨p, mapped⟩
  exact ⟨finalised, child, by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found,
    fun _ => rfl⟩

theorem holFmapAsFiniteSupportParamWitness_holesStill_rangeUpdate_f {α β : Type}
    (f : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_rangeUpdate_refs {β γ : Type}
    (refs : HolFiniteMapExact β (Ref γ)) : mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- Updating a mapped location preserves unfinalised holes outside the map range. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_still_not_finalised_frange_update"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem holesStill_rangeUpdate {α β γ : Type} [DecidableEq β] (f : HolFiniteMapExact α β)
    (p : α) (key : β) (value : Ref γ) (refs : HolFiniteMapExact β (Ref γ))
    (mapped : f.lookup p = some key) : holesStillNotFinalised f refs (refs.updateEq (key, value)) := by
  intro ptr outside ⟨tag, left, child, right, found⟩
  have different : ptr ≠ key := by
    intro equal
    subst ptr
    exact outside ⟨p, mapped⟩
  exact ⟨tag, left, child, right, by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found⟩

theorem holFmapAsFiniteSupportParamWitness_onlyFresh_trans_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_onlyFresh_trans_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl
theorem holFmapAsFiniteSupportParamWitness_onlyFresh_trans_h (h : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup h) h.finiteSupport = h := by cases h; rfl
theorem holFmapAsFiniteSupportParamWitness_onlyFresh_trans_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_onlyFresh_trans_middle (middle : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup middle) middle.finiteSupport = middle := by cases middle; rfl

/-- Freshness composes when the intermediate heap retains its old domain. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "only_fresh_trans"
  (fmap_as_finite_support_parameters := [f, g, h, refs, middle])]
theorem onlyFresh_trans (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat) (h : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (middle : HolFiniteMapExact Nat (Ref Value))
    (first : onlyFresh f g refs) (second : onlyFresh g h middle)
    (domain : refs.domain ⊆ middle.domain) : onlyFresh f h refs := by
  intro ptr ⟨new, outside⟩
  by_cases intermediate : ptr ∈ mapRange g
  · exact first ptr ⟨intermediate, outside⟩
  · intro allocated
    exact second ptr ⟨new, intermediate⟩ (domain allocated)

theorem holFmapAsFiniteSupportParamWitness_holesStill_trans_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_trans_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_trans_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_trans_middle (middle : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup middle) middle.finiteSupport = middle := by cases middle; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_trans_final (final : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup final) final.finiteSupport = final := by cases final; rfl

/-- Unfinalised-hole preservation composes across fresh map extensions. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_still_not_finalised_trans"
  (fmap_as_finite_support_parameters := [f, g, refs, middle, final])]
theorem holesStill_trans {α : Type} (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (middle : HolFiniteMapExact Nat (Ref Value))
    (final : HolFiniteMapExact Nat (Ref Value)) (_changed : α)
    (first : holesStillNotFinalised f refs middle) (second : holesStillNotFinalised g middle final)
    (fresh : onlyFresh f g refs) (_submap : finiteSubmap f g) : holesStillNotFinalised f refs final := by
  intro ptr outside hole
  have allocated : ptr ∈ refs.domain := by
    obtain ⟨tag, left, child, right, found⟩ := hole
    simp [HolFiniteMapExact.domain, found]
  have outsideNew := nonFresh_not_in_range f g refs ptr allocated outside fresh
  exact second ptr outsideNew (first ptr outside hole)

theorem holFmapAsFiniteSupportParamWitness_fresh_not_in_range_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_fresh_not_in_range_source (source : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup source) source.finiteSupport = source := by cases source; rfl
theorem holFmapAsFiniteSupportParamWitness_fresh_not_in_range_target (target : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup target) target.finiteSupport = target := by cases target; rfl

/-- A fresh target reference is outside the current pointer-map range. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "fresh_not_in_range_f"
  (fmap_as_finite_support_parameters := [f, source, target])]
theorem fresh_not_in_range (f : HolFiniteMapExact Nat Nat) (source : HolFiniteMapExact Nat (Ref Value))
    (target : HolFiniteMapExact Nat (Ref Value)) (related : stateRefRel f source target) :
    leastUnusedRef target ∉ mapRange f := by
  rintro ⟨key, mapped⟩
  obtain ⟨_, _, _, found, _⟩ := stateRefRel_lookup f key (leastUnusedRef target) source target mapped related
  rw [leastUnusedRef_unused] at found
  contradiction

end Flapjack.Compiler.Backend.BviTmc
