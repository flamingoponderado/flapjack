module

public import Flapjack.Compiler.Backend.WordAlloc.KeyMaps
public import Flapjack.Misc.Sptree.ToAList

@[expose] public section

namespace Flapjack.WordAlloc

/-- Flapjack factoring of external HOL fromAList support; no separate CakeML
original. First-match lookup affects payloads, not membership of a key. -/
private theorem domainFromAList {α : Type} (entries : List (Nat × α)) (key : Nat) :
    sptDomain (sptFromAList entries) key ↔ ∃ value, (key, value) ∈ entries := by
  induction entries with
  | nil => simp [sptDomain, sptFromAList]
  | cons entry entries ih =>
      rcases entry with ⟨other, value⟩
      by_cases h : key = other
      · subst key
        simp [sptDomain, sptFromAList, sptLookup_sptInsert_same]
      · simp [sptDomain, sptFromAList, sptLookup_sptInsert_ne other key value _ h,
          List.mem_cons, h, ← ih, sptDomain]

/-- HOL's full image-domain equality, including arbitrary collisions in f. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "apply_nummap_key_domain"]
theorem applyNummapKeyDomain {α : Type} (f : Nat → Nat) (names : Spt α) :
    sptDomain (applyNummapKey f names) =
      (fun key => ∃ source, sptDomain names source ∧ f source = key) := by
  funext key
  apply propext
  rw [applyNummapKey, domainFromAList]
  constructor
  · rintro ⟨value, hmem⟩
    obtain ⟨⟨source, payload⟩, hsource, heq⟩ := List.mem_map.mp hmem
    have hlookup := (sptMemToAList names source payload).mp hsource
    exact ⟨source, by simp [sptDomain, hlookup], (Prod.mk.inj heq).1⟩
  · rintro ⟨source, hsource, heq⟩
    obtain ⟨value, hlookup⟩ := (sptMem_iff_lookup source names).mp hsource
    refine ⟨value, List.mem_map.mpr ?_⟩
    exact ⟨(source, value), (sptMemToAList names source value).mpr hlookup, by simp [heq]⟩

end Flapjack.WordAlloc
