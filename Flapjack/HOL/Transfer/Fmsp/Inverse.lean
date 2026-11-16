module

public import Flapjack.HOL.Transfer.Fmsp
public import Flapjack.Misc.Sptree.Wf
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Canonical finite-map to sparse-tree conversion. -/
namespace Flapjack.HOL.Transfer.Fmsp

/-- Enumerate the bindings using any finite support, discarding absent keys.
    This is infrastructure for the source's order-independent map fold. -/
noncomputable def fm2spEntries {α : Type} (fm : HolFiniteMapExact Nat α) : List (Nat × α) :=
  (Classical.choose fm.finiteSupport).filterMap (fun k => (fm.lookup k).map (fun v => (k, v)))

private theorem entries_mem {α : Type} (fm : HolFiniteMapExact Nat α) (k : Nat) (v : α) :
    (k, v) ∈ fm2spEntries fm ↔ fm.lookup k = some v := by
  constructor
  · intro h
    obtain ⟨key, _, result⟩ := List.mem_filterMap.mp h
    cases found : fm.lookup key with
    | none => simp [found] at result
    | some value =>
      simp [found] at result
      rcases result with ⟨rfl, rfl⟩
      exact found
  · intro h
    apply List.mem_filterMap.mpr
    refine ⟨k, Classical.choose_spec fm.finiteSupport k (by simp [h]), ?_⟩
    simp [h]

/-- The finite-map parameter survives the canonical codec. -/
theorem holFmapAsFiniteSupportParamWitness_fm2sp_fm {α : Type}
    (fm : HolFiniteMapExact Nat α) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).lookup key = fm.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).finiteSupport = fm.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm) = fm := by
  cases fm
  exact ⟨rfl, rfl, rfl⟩

@[hol "HOL/src/transfer/examples/fmspScript.sml" "fm2sp_def"
  (fmap_as_finite_support_parameters := [fm])]
noncomputable def fm2sp {α : Type} (fm : HolFiniteMapExact Nat α) : Spt α :=
  sptFromAList (fm2spEntries fm)

/-- The lookup theorem uses the same canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_lookupFm2sp_fm {α : Type}
    (fm : HolFiniteMapExact Nat α) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).lookup key = fm.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).finiteSupport = fm.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm) = fm :=
  holFmapAsFiniteSupportParamWitness_fm2sp_fm fm key

@[hol "HOL/src/transfer/examples/fmspScript.sml" "lookup_fm2sp"
  (fmap_as_finite_support_parameters := [fm])]
theorem lookupFm2sp {α : Type} (k : Nat) (fm : HolFiniteMapExact Nat α) :
    sptLookup k (fm2sp fm) = fm.lookup k := by
  rw [fm2sp, sptLookup_sptFromAList]
  cases found : fm.lookup k with
  | none =>
    cases result : sptAListLookup k (fm2spEntries fm) with
    | none => rfl
    | some v =>
      have mem := sptAListLookup_mem k (fm2spEntries fm) v result
      have contradiction := (entries_mem fm k v).1 mem
      rw [found] at contradiction
      cases contradiction
  | some v =>
    apply sptAListLookup_eq_of_mem_unique
    · exact (entries_mem fm k v).2 found
    · intro other mem
      have h := (entries_mem fm k other).1 mem
      rw [found] at h
      exact Option.some.inj h.symm

/-- The well-formedness theorem uses the same canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_wfFm2sp_fm {α : Type}
    (fm : HolFiniteMapExact Nat α) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).lookup key = fm.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm)).finiteSupport = fm.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad fm) = fm :=
  holFmapAsFiniteSupportParamWitness_fm2sp_fm fm key

@[hol "HOL/src/transfer/examples/fmspScript.sml" "wf_fm2sp"
  (fmap_as_finite_support_parameters := [fm])]
theorem wfFm2sp {α : Type} (fm : HolFiniteMapExact Nat α) : sptWf (fm2sp fm) = true :=
  sptWfFromAList (fm2spEntries fm)

@[hol "HOL/src/transfer/examples/fmspScript.sml" "fm2sp_sp2fm"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem fm2spSp2fm {α : Type} (tree : Spt α) (hw : sptWf tree = true) :
    fm2sp (sp2fm tree) = tree := by
  apply (sptEqThm _ _ ⟨wfFm2sp _, hw⟩).mpr
  intro key
  exact lookupFm2sp key _

end Flapjack.HOL.Transfer.Fmsp
