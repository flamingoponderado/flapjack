import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockEnvironment

/-! Hole preservation during mutable-block finalisation. -/
namespace Flapjack.Compiler.Backend.BviTmc.FinaliseHoles
open BviTmc BvlSem

private def maptoBroadlookup {α β : Type} (f : HolFiniteMapExact α β) : α → Option β := f.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_finalised_f {α β : Type} (f : HolFiniteMapExact α β) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_finalised_old {β γ : Type} (old : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup old) old.finiteSupport = old := by cases old; rfl
theorem holFmapAsFiniteSupportParamWitness_holesUnchanged_finalised_new {β γ : Type} (new : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup new) new.finiteSupport = new := by cases new; rfl

/-- Restoring a removed mutable block with the same child preserves holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_unchanged_except_finalised"
  (fmap_as_finite_support_parameters := [f, old, new])]
theorem holesUnchanged_finalised {α β γ δ : Type} (f : HolFiniteMapExact α β) (_p : δ) (ptr : β)
    (old : HolFiniteMapExact β (Ref γ)) (new : HolFiniteMapExact β (Ref γ))
    (tag : Nat) (fin1 : Bool) (left : List γ) (child : γ) (right : List γ) (fin2 : Bool)
    (related : holesUnchangedExcept f (@HolFiniteMapExact.eraseEq β (Ref γ) (Classical.decEq β) old ptr) new ∅)
    (found : old.lookup ptr = some (.mutBlock tag fin1 left child right)) (_outside : ptr ∉ mapRange f) :
    holesUnchangedExcept f old
      (@HolFiniteMapExact.updateEq β (Ref γ) (Classical.decEq β) new (ptr, .mutBlock tag fin2 left child right)) ∅ := by
  classical
  intro key otherTag otherFin otherLeft otherChild otherRight keyOutside keyFound
  by_cases same : key = ptr
  · subst key
    rw [found] at keyFound
    cases keyFound
    refine ⟨fin2, child, ?_, fun _ => rfl⟩
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · have erased : (old.eraseEq ptr).lookup key = some (.mutBlock otherTag otherFin otherLeft otherChild otherRight) := by
      simpa [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, same] using keyFound
    obtain ⟨newFin, newChild, lookup, sameChild⟩ := related key otherTag otherFin otherLeft otherChild otherRight keyOutside erased
    refine ⟨newFin, newChild, ?_, sameChild⟩
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using lookup

theorem holFmapAsFiniteSupportParamWitness_holesStill_sub_f {α β : Type} (f : HolFiniteMapExact α β) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_sub_refs {β γ : Type} (refs : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_sub_refsNew {β γ : Type} (refsNew : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup refsNew) refsNew.finiteSupport = refsNew := by cases refsNew; rfl

/-- Removing a location absent from the old domain preserves unfinalised holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_still_not_finalised_sub"
  (fmap_as_finite_support_parameters := [f, refs, refsNew])]
theorem holesStill_sub {α β γ : Type} (ptr : β) (refs : HolFiniteMapExact β (Ref γ))
    (f : HolFiniteMapExact α β) (refsNew : HolFiniteMapExact β (Ref γ))
    (absent : ptr ∉ refs.domain) (related : holesStillNotFinalised f refs refsNew) :
    holesStillNotFinalised f refs (@HolFiniteMapExact.eraseEq β (Ref γ) (Classical.decEq β) refsNew ptr) := by
  classical
  intro key outside original
  have different : key ≠ ptr := by
    intro equal
    subst key
    obtain ⟨tag, left, child, right, found⟩ := original
    exact absent (by simp [HolFiniteMapExact.domain, found])
  obtain ⟨tag, left, child, right, found⟩ := related key outside original
  exact ⟨tag, left, child, right, by simpa [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, different] using found⟩

theorem holFmapAsFiniteSupportParamWitness_holesStill_non_dom_f {α β : Type} (f : HolFiniteMapExact α β) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_non_dom_refs {β γ : Type} (refs : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_holesStill_non_dom_refsNew {β γ : Type} (refsNew : HolFiniteMapExact β (Ref γ)) :
    mapofBroad (maptoBroadlookup refsNew) refsNew.finiteSupport = refsNew := by cases refsNew; rfl

/-- Finalising a location outside the old domain preserves unfinalised holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "holes_still_not_finalised_non_dom"
  (fmap_as_finite_support_parameters := [f, refs, refsNew])]
theorem holesStill_non_dom {α β γ : Type} (f : HolFiniteMapExact α β)
    (refs : HolFiniteMapExact β (Ref γ)) (refsNew : HolFiniteMapExact β (Ref γ)) (ptr : β)
    (tag : Nat) (left : List γ) (child : γ) (right : List γ)
    (related : holesStillNotFinalised f refs refsNew) (absent : ptr ∉ refs.domain) :
    holesStillNotFinalised f refs
      (@HolFiniteMapExact.updateEq β (Ref γ) (Classical.decEq β) refsNew (ptr, .mutBlock tag true left child right)) := by
  classical
  intro key outside original
  have different : key ≠ ptr := by
    intro equal
    subst key
    obtain ⟨oldTag, oldLeft, oldChild, oldRight, found⟩ := original
    exact absent (by simp [HolFiniteMapExact.domain, found])
  obtain ⟨oldTag, oldLeft, oldChild, oldRight, found⟩ := related key outside original
  exact ⟨oldTag, oldLeft, oldChild, oldRight,
    by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found⟩

end Flapjack.Compiler.Backend.BviTmc.FinaliseHoles
