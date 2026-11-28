module

public import Flapjack.HOL.Transfer.Fmsp.Inverse
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Misc.SptreeLookup

@[expose] public section

/-!
# Domain and deletion of the sparse-tree conversion

Counterparts of `domain_fm2sp` and `fm2sp_delete` from
`cakeml/compiler/inference/unifyScript.sml`: the sparse tree of a finite map has
exactly the map's domain, and conversion commutes with deletion.

This module deliberately sits beside `Fmsp`/`Fmsp/Inverse` rather than inside
them: `FiniteMap.DomainExact` and `Misc.SptreeLookup` pull in the Mathlib tactic
prelude, which reserves the `alias` token and breaks `Flapjack.Test` files that
use it as an identifier. Keeping these imports out of the `Fmsp` chain leaves
the test suite unaffected.
-/

namespace Flapjack.HOL.Transfer.Fmsp

/-- Canonical-map witness for the `domain_fm2sp` map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_domainFm2sp_fm {α : Type}
    (fm : HolFiniteMapExact Nat α) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).lookup key = fm.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).finiteSupport = fm.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm) = fm := by
  cases fm
  exact ⟨rfl, rfl, rfl⟩

/-- Original `domain_fm2sp`: the sparse tree of a finite map has exactly the
map's domain. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "domain_fm2sp"
  (fmap_as_finite_support_parameters := [fm])]
theorem domainFm2sp {α : Type} (fm : HolFiniteMapExact Nat α) :
    sptDomain (fm2sp fm) = fm.domain := by
  funext key
  apply propext
  show (sptLookup key (fm2sp fm)).isSome = true ↔ fm.lookup key ≠ none
  rw [lookupFm2sp]
  simp [Option.isSome_iff_ne_none]

/-- Canonical-map witness for the `fm2sp_delete` map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fm2spDelete_fm {α : Type}
    (fm : HolFiniteMapExact Nat α) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).lookup key = fm.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).finiteSupport = fm.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm) = fm := by
  cases fm
  exact ⟨rfl, rfl, rfl⟩

/-- Original `fm2sp_delete`: conversion commutes with deletion. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "fm2sp_delete"
  (fmap_as_finite_support_parameters := [fm])]
theorem fm2spDelete {α : Type} (fm : HolFiniteMapExact Nat α) (k : Nat) :
    fm2sp (fm.eraseEq k) = sptDelete k (fm2sp fm) := by
  have hwfLeft : sptWf (fm2sp (fm.eraseEq k)) = true := wfFm2sp _
  have hwfRight : sptWf (sptDelete k (fm2sp fm)) = true :=
    sptWfDelete (fm2sp fm) k (wfFm2sp fm)
  rw [sptEqThm (fm2sp (fm.eraseEq k)) (sptDelete k (fm2sp fm)) ⟨hwfLeft, hwfRight⟩]
  intro n
  rw [lookupFm2sp, sptLookup_sptDelete, lookupFm2sp, HolFiniteMapExact.lookup_eraseEq]
  simp [FDOMSUB_HOL]

end Flapjack.HOL.Transfer.Fmsp
