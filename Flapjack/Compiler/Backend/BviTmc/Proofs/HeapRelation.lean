import Flapjack.Compiler.Backend.BviTmc.Proofs.ValueRelation
import Flapjack.FiniteMap.CardinalityExact

/-! Reference-map relations used by the TMC evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem

private def maptoBroadlookup {α β : Type} (f : HolFiniteMapExact α β) : α → Option β := f.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_stateRefRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_source (source : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup source) source.finiteSupport = source := by cases source; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_target (target : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup target) target.finiteSupport = target := by cases target; rfl

/-- Every original reference is translated to a related target reference,
and the pointer map is defined exactly on the source reference domain. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_ref_rel_def"
  (fmap_as_finite_support_parameters := [f, source, target])]
def stateRefRel (f : HolFiniteMapExact Nat Nat) (source : HolFiniteMapExact Nat (Ref Value))
    (target : HolFiniteMapExact Nat (Ref Value)) : Prop :=
  f.domain = source.domain ∧ ∀ i v, source.lookup i = some v →
    ∃ j w, f.lookup i = some j ∧ refRel f v w ∧ target.lookup j = some w

theorem holFmapAsFiniteSupportParamWitness_fmapInj_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Pointer renaming is injective on its finite domain. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "fmap_inj_def"
  (fmap_as_finite_support_parameters := [f])]
def fmapInj (f : HolFiniteMapExact Nat Nat) : Prop :=
  ∀ p1 p2 q, f.lookup p1 = some q ∧ f.lookup p2 = some q → p1 = p2

theorem holFmapAsFiniteSupportParamWitness_refRel_submap_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_refRel_submap_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl

/-- Extending the pointer map preserves the reference-cell relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "ref_rel_submap"
  (fmap_as_finite_support_parameters := [f, g])]
theorem refRel_submap (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat)
    (source target : Ref Value) (related : refRel f source target) (submap : finiteSubmap f g) :
    refRel g source target := by
  cases related with
  | byteArray b bytes => exact .byteArray b bytes
  | valueArray xs ys values => exact .valueArray xs ys (listRel_submap f g xs ys values submap)
  | thunk mode x y value => exact .thunk mode x y (valueRel_submap f g x y value submap)

theorem holFmapAsFiniteSupportParamWitness_fmapInj_update_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Extending the pointer map at a fresh target keeps it injective. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "fmap_inj_update"
  (fmap_as_finite_support_parameters := [f])]
theorem fmapInj_update (f : HolFiniteMapExact Nat Nat) (key value : Nat) (injective : fmapInj f)
    (fresh : ∀ key', f.lookup key' ≠ some value) : fmapInj (f.updateEq (key, value)) := by
  intro p1 p2 q ⟨h1, h2⟩
  by_cases eq1 : p1 = key <;> by_cases eq2 : p2 = key
  · exact eq1.trans eq2.symm
  · subst p1
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at h1
    subst q
    have old : f.lookup p2 = some value := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq2] using h2
    exact (fresh p2 old).elim
  · subst p2
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at h2
    subst q
    have old : f.lookup p1 = some value := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq1] using h1
    exact (fresh p1 old).elim
  · apply injective p1 p2 q
    exact ⟨by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq1] using h1,
      by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq2] using h2⟩

theorem holFmapAsFiniteSupportParamWitness_stateRefRel_filled_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_filled_source (source : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup source) source.finiteSupport = source := by cases source; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_filled_target (target : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup target) target.finiteSupport = target := by cases target; rfl

/-- Updating a target location outside the pointer-map range preserves the
reference relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_ref_rel_filled"
  (fmap_as_finite_support_parameters := [f, source, target])]
theorem stateRefRel_filled (f : HolFiniteMapExact Nat Nat) (source : HolFiniteMapExact Nat (Ref Value))
    (target : HolFiniteMapExact Nat (Ref Value)) (key : Nat) (value : Ref Value)
    (related : stateRefRel f source target) (fresh : ∀ i, f.lookup i ≠ some key) :
    stateRefRel f source (target.updateEq (key, value)) := by
  refine ⟨related.1, ?_⟩
  intro i v found
  obtain ⟨j, w, mapped, cells, lookup⟩ := related.2 i v found
  have different : j ≠ key := by
    intro equal
    subst j
    exact fresh i mapped
  refine ⟨j, w, mapped, cells, ?_⟩
  simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using lookup

theorem holFmapAsFiniteSupportParamWitness_stateRefRel_update_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_update_source (source : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup source) source.finiteSupport = source := by cases source; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_update_target (target : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup target) target.finiteSupport = target := by cases target; rfl

/-- Updating related source and target cells preserves the heap relation
when pointer renaming is injective. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_ref_rel_update"
  (fmap_as_finite_support_parameters := [f, source, target])]
theorem stateRefRel_update (f : HolFiniteMapExact Nat Nat) (source : HolFiniteMapExact Nat (Ref Value))
    (target : HolFiniteMapExact Nat (Ref Value)) (ptr ptr' : Nat) (v w : Ref Value)
    (related : stateRefRel f source target) (injective : fmapInj f)
    (mapped : f.lookup ptr = some ptr') (cells : refRel f v w) :
    stateRefRel f (source.updateEq (ptr, v)) (target.updateEq (ptr', w)) := by
  constructor
  · apply Set.ext
    intro i
    by_cases eq : i = ptr
    · subst i
      simp [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, mapped]
    · have same := Set.ext_iff.mp related.1 i
      simpa [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using same
  · intro i old found
    by_cases eq : i = ptr
    · subst i
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at found
      subst old
      exact ⟨ptr', w, mapped, cells, by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]⟩
    · have oldFound : source.lookup i = some old := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using found
      obtain ⟨j, cell, rename, cellsRel, targetFound⟩ := related.2 i old oldFound
      have different : j ≠ ptr' := by
        intro same
        subst j
        exact eq (injective i ptr ptr' ⟨rename, mapped⟩)
      exact ⟨j, cell, rename, cellsRel, by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using targetFound⟩

theorem holFmapAsFiniteSupportParamWitness_stateRefRel_alloc_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_alloc_source (source : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup source) source.finiteSupport = source := by cases source; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_alloc_target (target : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup target) target.finiteSupport = target := by cases target; rfl

/-- Fresh source and target allocation extends the pointer map and keeps
the reference heaps related. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_ref_rel_alloc"
  (fmap_as_finite_support_parameters := [f, source, target])]
theorem stateRefRel_alloc (f : HolFiniteMapExact Nat Nat) (source : HolFiniteMapExact Nat (Ref Value))
    (target : HolFiniteMapExact Nat (Ref Value)) (src tgt : Nat) (v w : Ref Value)
    (related : stateRefRel f source target) (srcFresh : src ∉ source.domain) (_tgtFresh : tgt ∉ target.domain)
    (rangeFresh : ∀ i, f.lookup i ≠ some tgt) (cells : refRel (f.updateEq (src, tgt)) v w) :
    stateRefRel (f.updateEq (src, tgt)) (source.updateEq (src, v)) (target.updateEq (tgt, w)) := by
  have mapMissing : f.lookup src = none := by
    have notMem : src ∉ f.domain := by rw [related.1]; exact srcFresh
    simpa [HolFiniteMapExact.domain] using notMem
  have extension : finiteSubmap f (f.updateEq (src, tgt)) := by
    intro i j found
    have ne : i ≠ src := by
      intro eq
      subst i
      rw [mapMissing] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found
  constructor
  · apply Set.ext
    intro i
    by_cases eq : i = src
    · subst i
      simp [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · have same := Set.ext_iff.mp related.1 i
      simpa [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using same
  · intro i old found
    by_cases eq : i = src
    · subst i
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at found
      subst old
      exact ⟨tgt, w, by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL], cells,
        by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]⟩
    · have oldFound : source.lookup i = some old := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using found
      obtain ⟨j, cell, rename, cellsRel, targetFound⟩ := related.2 i old oldFound
      have different : j ≠ tgt := by
        intro same
        subst j
        exact rangeFresh i rename
      exact ⟨j, cell, extension i j rename, refRel_submap f (f.updateEq (src, tgt)) old cell cellsRel extension,
        by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using targetFound⟩

theorem holFmapAsFiniteSupportParamWitness_stateRefRel_lookup_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_lookup_source (source : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup source) source.finiteSupport = source := by cases source; rfl
theorem holFmapAsFiniteSupportParamWitness_stateRefRel_lookup_target (target : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup target) target.finiteSupport = target := by cases target; rfl

/-- Every mapped source pointer resolves to related cells in both heaps. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_ref_rel_lookup"
  (fmap_as_finite_support_parameters := [f, source, target])]
theorem stateRefRel_lookup (f : HolFiniteMapExact Nat Nat) (n m : Nat)
    (source : HolFiniteMapExact Nat (Ref Value)) (target : HolFiniteMapExact Nat (Ref Value))
    (mapped : f.lookup n = some m) (related : stateRefRel f source target) :
    ∃ v w, source.lookup n = some v ∧ target.lookup m = some w ∧ refRel f v w := by
  have member : n ∈ source.domain := by
    rw [← related.1]
    simp [HolFiniteMapExact.domain, mapped]
  cases found : source.lookup n with
  | none => simp [HolFiniteMapExact.domain, found] at member
  | some v =>
    obtain ⟨j, w, rename, cells, targetFound⟩ := related.2 n v found
    rw [mapped] at rename
    have equal : m = j := Option.some.inj rename
    subst j
    exact ⟨v, w, rfl, targetFound, cells⟩

theorem holFmapAsFiniteSupportParamWitness_fmapInj_lookup_eq_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- An injective pointer map identifies target pointers exactly when it
identifies their source pointers. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "fmap_inj_flookup_eq"
  (fmap_as_finite_support_parameters := [f])]
theorem fmapInj_lookup_eq (f : HolFiniteMapExact Nat Nat) (n m n' m' : Nat)
    (injective : fmapInj f) (left : f.lookup n = some m) (right : f.lookup n' = some m') :
    m = m' ↔ n = n' := by
  constructor
  · intro equal
    subst m'
    exact injective n n' m ⟨left, right⟩
  · intro equal
    subst n'
    rw [left] at right
    exact Option.some.inj right

end Flapjack.Compiler.Backend.BviTmc
