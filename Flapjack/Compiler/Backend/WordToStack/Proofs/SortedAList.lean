import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedKeys
import Flapjack.Misc.Sptree

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.Compiler.Backend.WordToStack

/-- Full original head/tail descending-key result, in the original conjunct
order. Payload types are arbitrary; comparisons observe natural keys only. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_CONS_IMP"]
theorem sortedConsImp {α : Type} (h : Nat × α) (t : List (Nat × α))
    (hs : descendingKeys (h :: t)) :
    h ∉ t ∧ descendingKeys t ∧ ∀ x, x ∈ t → h.1 > x.1 := by
  obtain ⟨ht, hn, hb⟩ := sortedFstLessImp t h hs
  exact ⟨hn, ht, hb⟩

/-- Full original strict descending-key lists have distinct keys. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "SORTED_IMP_ALL_DISTINCT_LEMMA"]
theorem sortedImpAllDistinctLemma {α : Type} (l : List (Nat × α))
    (hs : descendingKeys l) : (l.map Prod.fst).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨_, ht, hb⟩ := sortedConsImp x xs hs
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih ht⟩
    intro hmem
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hmem
    have := hb y hy
    omega

/-- Flapjack infrastructure: numeric first-match association lookup equals
membership when keys are distinct. No generic external-library declaration is
claimed for this numeric helper; no payload equality instance is needed. -/
private theorem lookupIffMem {α : Type} (l : List (Nat × α)) (q : Nat) (r : α)
    (hd : (l.map Prod.fst).Nodup) : sptAListLookup q l = some r ↔ (q, r) ∈ l := by
  constructor
  · exact sptAListLookup_mem q l r
  · intro hm
    induction l with
    | nil => simp at hm
    | cons x xs ih =>
      rcases x with ⟨key, val⟩
      obtain ⟨hn, ht⟩ := (List.nodup_cons.mp hd)
      rcases List.mem_cons.mp hm with he | hm
      · cases he
        simp [sptAListLookup]
      · have hne : q ≠ key := by
          intro he
          apply hn
          exact List.mem_map.mpr ⟨(q,r), hm, he⟩
        simpa [sptAListLookup, hne] using ih ht hm

/-- Flapjack infrastructure: the existing unrestricted native mixed-order
Spt enumeration bridge, expressed at arbitrary key/value membership. There is
no separate CakeML original for this local restatement. -/
private theorem nativeToAListMemIffLookup {α : Type} (tree : Spt α) (key : Nat) (value : α) :
    (key, value) ∈ sptToAList tree ↔ sptLookup key tree = some value := by
  constructor
  · intro hm
    rcases sptFoldi_mem_address tree 0 [] key value hm with ha | ⟨localKey, he, hl⟩
    · simp at ha
    · have hk : key = localKey := by simpa [sptAcc_eq, lrNext] using he
      simpa [hk] using hl
  · intro hl
    simpa [sptToAList, sptAcc_eq, lrNext] using
      sptFoldi_lookup_mem tree 0 [] key value hl

/-- Full original distinct-key Spt association-list roundtrip membership law,
with native first-match insertion and native mixed-order enumeration. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "ALL_DISTINCT_MEM_toAList_fromAList"]
theorem allDistinctMemToAListFromAList {α : Type} (ls : List (Nat × α)) (x : Nat × α)
    (hd : (ls.map Prod.fst).Nodup) :
    x ∈ sptToAList (sptFromAList ls) ↔ x ∈ ls := by
  rcases x with ⟨key, value⟩
  rw [nativeToAListMemIffLookup, sptLookup_sptFromAList]
  exact lookupIffMem ls key value hd

/-- Full original sorted-list native Spt roundtrip membership equality. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MEM_toAList_fromAList"]
theorem memToAListFromAList {α : Type} (l : List (Nat × α)) (a : Nat × α)
    (hs : descendingKeys l) :
    (a ∈ sptToAList (sptFromAList l)) = (a ∈ l) := by
  exact propext (allDistinctMemToAListFromAList l a (sortedImpAllDistinctLemma l hs))

/-- Full original uniqueness: a sorted permutation of the actual native Spt
roundtrip is the original sorted list. No roundtrip or membership fact is
assumed; both are derived from native operations and the original guards. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "SORTED_FST_PERM_IMP_ALIST_EQ"]
theorem sortedFstPermImpAListEq {α : Type} (l q : List (Nat × α))
    (hl : descendingKeys l) (hq : descendingKeys q)
    (hp : List.Perm (sptToAList (sptFromAList l)) q) : q = l := by
  apply (sortedImpEqLists l q hq hl ?_).symm
  intro x
  exact hp.mem_iff.symm.trans (allDistinctMemToAListFromAList l x
    (sortedImpAllDistinctLemma l hl))

end Flapjack.WordToStackProofs
