import Flapjack.Compiler.Backend.BviTmc.Proofs.HoleRelation

/-! Heap-level infrastructure for the TMC constant-construction simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem

/-- Fresh allocation in related heaps extends the renaming, retains the old
target domain, and preserves mutable-hole invariants. This Flapjack helper
packages the source proof's allocation steps for constant construction. -/
theorem freshHeapAllocation (f : HolFiniteMapExact Nat Nat)
    (source : HolFiniteMapExact Nat (Ref Value)) (target : HolFiniteMapExact Nat (Ref Value))
    (v w : Ref Value) (related : stateRefRel f source target) (injective : fmapInj f)
    (cells : refRel f v w) :
    let src := leastUnusedRef source
    let tgt := leastUnusedRef target
    let next := f.updateEq (src, tgt)
    next.lookup src = some tgt ∧
    stateRefRel next (source.updateEq (src, v)) (target.updateEq (tgt, w)) ∧
    fmapInj next ∧ finiteSubmap f next ∧ onlyFresh f next target ∧
    holesUnchangedExcept f target (target.updateEq (tgt, w)) ∅ ∧
    holesStillNotFinalised f target (target.updateEq (tgt, w)) ∧
    target.domain ⊆ (target.updateEq (tgt, w)).domain := by
  dsimp only
  let src := leastUnusedRef source
  let tgt := leastUnusedRef target
  change (f.updateEq (src, tgt)).lookup src = some tgt ∧
    stateRefRel (f.updateEq (src, tgt)) (source.updateEq (src, v)) (target.updateEq (tgt, w)) ∧
    fmapInj (f.updateEq (src, tgt)) ∧ finiteSubmap f (f.updateEq (src, tgt)) ∧
    onlyFresh f (f.updateEq (src, tgt)) target ∧
    holesUnchangedExcept f target (target.updateEq (tgt, w)) ∅ ∧
    holesStillNotFinalised f target (target.updateEq (tgt, w)) ∧
    target.domain ⊆ (target.updateEq (tgt, w)).domain
  have sourceAbsent : source.lookup src = none := leastUnusedRef_unused source
  have targetAbsent : target.lookup tgt = none := leastUnusedRef_unused target
  have srcFresh : src ∉ source.domain := by simp [HolFiniteMapExact.domain, sourceAbsent]
  have tgtFresh : tgt ∉ target.domain := by simp [HolFiniteMapExact.domain, targetAbsent]
  have outside : tgt ∉ mapRange f := fresh_not_in_range f source target related
  have mapMissing : f.lookup src = none := by
    have absent : src ∉ f.domain := by rw [related.1]; exact srcFresh
    simpa [HolFiniteMapExact.domain] using absent
  have extension : finiteSubmap f (f.updateEq (src, tgt)) := by
    intro key value found
    have different : key ≠ src := by
      intro equal
      subst key
      rw [mapMissing] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found
  have notRange : ∀ key, f.lookup key ≠ some tgt := by
    intro key found
    exact outside ⟨key, found⟩
  refine ⟨by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
    stateRefRel_alloc f source target src tgt v w related srcFresh tgtFresh notRange
      (refRel_submap f _ v w cells extension),
    fmapInj_update f src tgt injective notRange, extension, ?_, ?_, ?_, ?_⟩
  · intro ptr ⟨⟨key, found⟩, absent⟩
    by_cases equal : key = src
    · subst key
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at found
      subst ptr
      exact tgtFresh
    · have old : f.lookup key = some ptr := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal] using found
      exact (absent ⟨key, old⟩).elim
  · intro ptr tag finalised left child right _ found
    have different : ptr ≠ tgt := by
      intro equal
      subst ptr
      rw [targetAbsent] at found
      contradiction
    exact ⟨finalised, child, by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found,
      fun _ => rfl⟩
  · intro ptr _ ⟨tag, left, child, right, found⟩
    have different : ptr ≠ tgt := by
      intro equal
      subst ptr
      rw [targetAbsent] at found
      contradiction
    exact ⟨tag, left, child, right, by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found⟩
  · intro ptr allocated
    by_cases equal : ptr = tgt
    · subst ptr
      simp [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · simpa [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal] using allocated

private theorem relatedMap (f : HolFiniteMapExact Nat Nat) (m m' : Nat → Value)
    (related : ∀ key, valueRel f (m key) (m' key)) (indices : List Nat) :
    List.Forall₂ (valueRel f) (indices.map m) (indices.map m') := by
  induction indices with
  | nil => exact .nil
  | cons key rest ih => exact .cons (related key) ih

/-- One constant component preserves the heap simulation. Strings allocate
corresponding byte arrays; the other components leave the heaps unchanged.
This Flapjack helper supports the recursive source construction theorem. -/
theorem doPart_related (f : HolFiniteMapExact Nat Nat) (m m' : Nat → Value)
    (part : ClosLang.ConstPart) (source : HolFiniteMapExact Nat (Ref Value))
    (target : HolFiniteMapExact Nat (Ref Value)) (related : stateRefRel f source target)
    (injective : fmapInj f) (values : ∀ key, valueRel f (m key) (m' key)) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : HolFiniteMapExact Nat (Ref Value)),
      doPart m' part target = (value', targetNext) ∧
      valueRel nextMap (doPart m part source).1 value' ∧
      stateRefRel nextMap (doPart m part source).2 targetNext ∧ fmapInj nextMap ∧
      finiteSubmap f nextMap ∧ onlyFresh f nextMap target ∧
      holesUnchangedExcept f target targetNext ∅ ∧ holesStillNotFinalised f target targetNext ∧
      target.domain ⊆ targetNext.domain := by
  cases part with
  | int i =>
    refine ⟨f, .number i, target, rfl, .number i, related, injective, ?_, onlyFresh_refl f target,
      holesUnchanged_refl f target ∅, holesStill_refl f target, Set.Subset.rfl⟩
    intro key value found
    exact found
  | w64 word =>
    refine ⟨f, .word64 word, target, rfl, .word64 word, related, injective, ?_, onlyFresh_refl f target,
      holesUnchanged_refl f target ∅, holesStill_refl f target, Set.Subset.rfl⟩
    intro key value found
    exact found
  | con tag indices =>
    refine ⟨f, .block tag (indices.map m'), target, rfl, .block _ _ _ (relatedMap f m m' values indices),
      related, injective, ?_, onlyFresh_refl f target, holesUnchanged_refl f target ∅,
      holesStill_refl f target, Set.Subset.rfl⟩
    intro key value found
    exact found
  | str text =>
    have ⟨mapped, heaps, inj, extension, fresh, holes, unfinalised, domain⟩ :=
      freshHeapAllocation f source target (.byteArray true text.explode) (.byteArray true text.explode)
        related injective (.byteArray _ _)
    exact ⟨f.updateEq (leastUnusedRef source, leastUnusedRef target), .refPtr true (leastUnusedRef target),
      target.updateEq (leastUnusedRef target, .byteArray true text.explode), rfl,
      .refPtr _ _ true mapped, heaps, inj, extension, fresh, holes, unfinalised, domain⟩

/-- Sequential component construction preserves related heaps and values.
The domain conclusion is Flapjack infrastructure used to compose freshness. -/
theorem doBuild_related (parts : List ClosLang.ConstPart) (f : HolFiniteMapExact Nat Nat)
    (m m' : Nat → Value) (i : Nat) (source : HolFiniteMapExact Nat (Ref Value))
    (target : HolFiniteMapExact Nat (Ref Value)) (related : stateRefRel f source target)
    (injective : fmapInj f) (values : ∀ key, valueRel f (m key) (m' key)) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : HolFiniteMapExact Nat (Ref Value)),
      doBuild m' i parts target = (value', targetNext) ∧
      valueRel nextMap (doBuild m i parts source).1 value' ∧
      stateRefRel nextMap (doBuild m i parts source).2 targetNext ∧ fmapInj nextMap ∧
      finiteSubmap f nextMap ∧ onlyFresh f nextMap target ∧
      holesUnchangedExcept f target targetNext ∅ ∧ holesStillNotFinalised f target targetNext ∧
      target.domain ⊆ targetNext.domain := by
  induction parts generalizing f m m' i source target with
  | nil =>
    refine ⟨f, m' (i - 1), target, rfl, values _, related, injective, ?_, onlyFresh_refl f target,
      holesUnchanged_refl f target ∅, holesStill_refl f target, Set.Subset.rfl⟩
    intro key value found
    exact found
  | cons part parts ih =>
    obtain ⟨midMap, midValue, midTarget, targetPart, partValue, midHeaps, midInj,
      firstSubmap, firstFresh, firstHoles, firstStill, firstDomain⟩ :=
      doPart_related f m m' part source target related injective values
    cases sourcePart : doPart m part source with
    | mk sourceValue midSource =>
      simp only [sourcePart] at partValue midHeaps
      have nextValues : ∀ key, valueRel midMap
          (if key = i then sourceValue else m key) (if key = i then midValue else m' key) := by
        intro key
        by_cases equal : key = i
        · simp [equal, partValue]
        · simp only [equal, ↓reduceIte]
          exact valueRel_submap f midMap _ _ (values key) firstSubmap
      obtain ⟨lastMap, lastValue, lastTarget, targetRun, resultRel, lastHeaps, lastInj,
        secondSubmap, secondFresh, secondHoles, secondStill, secondDomain⟩ :=
        ih midMap (fun key => if key = i then sourceValue else m key)
          (fun key => if key = i then midValue else m' key) (i + 1) midSource midTarget
          midHeaps midInj nextValues
      refine ⟨lastMap, lastValue, lastTarget, ?_, ?_, ?_, lastInj, ?_,
        onlyFresh_trans f midMap lastMap target midTarget firstFresh secondFresh firstDomain,
        holesUnchanged_trans f midMap target midTarget lastTarget ∅ firstHoles secondHoles firstFresh firstSubmap,
        holesStill_trans f midMap target midTarget lastTarget () firstStill secondStill firstFresh firstSubmap,
        firstDomain.trans secondDomain⟩
      · simpa [doBuild, targetPart] using targetRun
      · simpa [doBuild, sourcePart] using resultRel
      · simpa [doBuild, sourcePart] using lastHeaps
      · intro key value found
        exact secondSubmap key value (firstSubmap key value found)

/-- The source constant-building loop preserves the value and heap relations,
including freshness and hole invariants across every component. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_build_v_rel"
  (fmap_as_finite_support_relation := [source, sourceNext, f, target, nextMap, targetNext])]
theorem doBuild_value_rel (parts : List ClosLang.ConstPart) (m : Nat → Value) (i : Nat)
    (source : HolFiniteMapExact Nat (Ref Value)) (value : Value)
    (sourceNext : HolFiniteMapExact Nat (Ref Value)) (f : HolFiniteMapExact Nat Nat)
    (m' : Nat → Value) (target : HolFiniteMapExact Nat (Ref Value))
    (run : doBuild m i parts source = (value, sourceNext)) (related : stateRefRel f source target)
    (injective : fmapInj f) (values : ∀ key, valueRel f (m key) (m' key)) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : HolFiniteMapExact Nat (Ref Value)),
      doBuild m' i parts target = (value', targetNext) ∧ valueRel nextMap value value' ∧
      stateRefRel nextMap sourceNext targetNext ∧ fmapInj nextMap ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target ∧ holesUnchangedExcept f target targetNext ∅ ∧
      holesStillNotFinalised f target targetNext := by
  obtain ⟨nextMap, value', targetNext, targetRun, result, heaps, inj, submap, fresh, holes, still, _⟩ :=
    doBuild_related parts f m m' i source target related injective values
  simp only [run] at result heaps
  exact ⟨nextMap, value', targetNext, targetRun, result, heaps, inj, submap, fresh, holes, still⟩

/-- Source constant construction preserves the value and heap relations. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_build_const_v_rel"
  (fmap_as_finite_support_relation := [source, sourceNext, f, target, nextMap, targetNext])]
theorem doBuildConst_value_rel (parts : List ClosLang.ConstPart)
    (source : HolFiniteMapExact Nat (Ref Value)) (value : Value)
    (sourceNext : HolFiniteMapExact Nat (Ref Value)) (f : HolFiniteMapExact Nat Nat)
    (target : HolFiniteMapExact Nat (Ref Value))
    (run : doBuildConst parts source = (value, sourceNext)) (related : stateRefRel f source target)
    (injective : fmapInj f) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : HolFiniteMapExact Nat (Ref Value)),
      doBuildConst parts target = (value', targetNext) ∧ valueRel nextMap value value' ∧
      stateRefRel nextMap sourceNext targetNext ∧ fmapInj nextMap ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target ∧ holesUnchangedExcept f target targetNext ∅ ∧
      holesStillNotFinalised f target targetNext := by
  exact doBuild_value_rel parts (fun _ => .number 0) 0 source value sourceNext f
    (fun _ => .number 0) target run related injective (fun _ => .number 0)

end Flapjack.Compiler.Backend.BviTmc
