import Flapjack.Misc.Sptree

namespace Flapjack

/-- Full HOL domain-and-lookup characterization of subspt. The untagged
predicate rendering above uses this exact characteristic-set equation; this
is the original theorem, rather than a tag on an unrelated definition. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "subspt_def"]
theorem sptSubsptDef {α : Type} (first second : Spt α) :
    sptSubspt first second ↔
      ∀ key, sptMem key first →
        sptMem key second ∧ sptLookup key second = sptLookup key first := Iff.rfl

/-- Full original pointwise lookup characterization, over arbitrary values. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "subspt_lookup"]
theorem sptSubsptLookup {α : Type} (first second : Spt α) :
    sptSubspt first second ↔
      ∀ key value, sptLookup key first = some value → sptLookup key second = some value := by
  constructor
  · intro relation key value lookup
    have member : sptMem key first := by simp [sptMem, sptDomain, lookup]
    have equality := (relation key member).2
    simpa only [lookup] using equality
  · intro lookup key member
    cases found : sptLookup key first with
    | none => simp [sptMem, sptDomain, found] at member
    | some value =>
      have target := lookup key value found
      exact ⟨by simp [sptMem, sptDomain, target], target⟩

/-- Full original subspt transitivity, without extra carrier assumptions. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "subspt_trans"]
theorem sptSubsptTrans {α : Type} (first second third : Spt α)
    (relation : sptSubspt first second ∧ sptSubspt second third) :
    sptSubspt first third := by
  intro key member
  obtain ⟨middleMember, firstEq⟩ := relation.1 key member
  obtain ⟨lastMember, secondEq⟩ := relation.2 key middleMember
  exact ⟨lastMember, secondEq.trans firstEq⟩

/-- Full original left-biased union monotonicity. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "subspt_union"]
theorem sptSubsptUnion {α : Type} (first second : Spt α) :
    sptSubspt first (sptUnion first second) := by
  rw [sptSubsptLookup]
  intro key value lookup
  rw [sptLookup_sptUnion, lookup]

/-- Full original union-fold monotonicity. List order, left accumulator, generic
payload and the actual native sptUnion are retained. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "subspt_FOLDL_union"]
theorem sptSubsptFoldlUnion {α : Type} (trees : List (Spt α)) (initial : Spt α) :
    sptSubspt initial (trees.foldl sptUnion initial) := by
  induction trees generalizing initial with
  | nil =>
      intro key member
      exact ⟨member, rfl⟩
  | cons first rest ih =>
      exact sptSubsptTrans initial (sptUnion initial first)
        (rest.foldl sptUnion (sptUnion initial first))
        ⟨sptSubsptUnion initial first, ih (sptUnion initial first)⟩

end Flapjack
