module

public import Flapjack.FiniteMap.Basic

@[expose] public section

/-! Canonical finite-support map carrier and its basic operations. -/
namespace Flapjack

/-- Flapjack finite-support map infrastructure: a total lookup function with a
proof that its defined domain is finite. This models HOL `fmap` observations
but is not separately tagged as the generic finite-map type declaration. -/
structure HolFiniteMapExact (α β : Type) where
  lookup : α → Option β
  finiteSupport : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys

namespace HolFiniteMapExact

/-- Flapjack encoding of HOL `FMAP_MAP2`: preserve keys and map each present
value with the key available to the callback. -/
def map2 (f : α × β → γ) (map : HolFiniteMapExact α β) :
    HolFiniteMapExact α γ where
  lookup key := (map.lookup key).map (fun value => f (key, value))
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨keys, ?_⟩
    intro key hlookup
    apply hkeys key
    cases hsource : map.lookup key <;> simp [hsource] at hlookup ⊢

@[simp] theorem lookup_map2 (f : α × β → γ)
    (map : HolFiniteMapExact α β) (key : α) :
    (map.map2 f).lookup key = (map.lookup key).map (fun value => f (key, value)) := rfl

/-- HOL `FEMPTY` on the finite-support carrier: the everywhere-undefined map.
    Its support witness is the empty key list. -/
def empty : HolFiniteMapExact α β where
  lookup _ := none
  finiteSupport := ⟨[], by intro key h; exact absurd rfl h⟩

/-- HOL `FUPDATE` (`|+`) on the finite-support carrier: the updated key is added
    to the support list, so the result keeps an explicit finite support. -/
def update [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β) (entry : α × β) :
    HolFiniteMapExact α β where
  lookup := FUPDATE map.lookup entry
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨entry.1 :: keys, ?_⟩
    intro key hlookup
    by_cases h : entry.1 == key
    · have hk : entry.1 = key := beq_iff_eq.mp h
      subst hk
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply hkeys
      simpa [FUPDATE, h] using hlookup

/-- HOL `FUPDATE_LIST` (`|++`) on the finite-support carrier, matching the raw
    finite-map `FUPDATE_LIST` (`foldl FUPDATE`). Each update adds its key to the
    support, so the result is finite-support by construction. -/
def updateList [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β)
    (entries : List (α × β)) : HolFiniteMapExact α β where
  lookup := FUPDATE_LIST map.lookup entries
  finiteSupport := by
    induction entries generalizing map with
    | nil => simpa [FUPDATE_LIST] using map.finiteSupport
    | cons entry entries ih =>
      simpa [FUPDATE_LIST_cons, update] using ih (update map entry)

/-- HOL domain subtraction (`\\`) on the finite-support carrier: removing a key
    can only shrink the support, so the original witness still covers it. -/
def erase [BEq α] (map : HolFiniteMapExact α β) (key : α) :
    HolFiniteMapExact α β where
  lookup := FDOMSUB map.lookup key
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨keys, ?_⟩
    intro k hk
    apply hkeys k
    by_cases h : key == k
    · simp [FDOMSUB, h] at hk
    · simpa [FDOMSUB, h] using hk

/-- HOL `res_var` on the finite-support carrier (`crepSemScript.sml:163`):
    `NONE` subtracts the key from the domain, `SOME v` updates it. -/
def resVar [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β)
    (entry : α × Option β) : HolFiniteMapExact α β :=
  match entry.2 with
  | none => erase map entry.1
  | some value => update map (entry.1, value)

/-- HOL-equality (`=`) `FUPDATE` on the finite-support carrier, using
    `DecidableEq` (Lean's encoding of HOL `=`) rather than Boolean `BEq`. -/
def updateEq [DecidableEq α] (map : HolFiniteMapExact α β) (entry : α × β) :
    HolFiniteMapExact α β where
  lookup := FUPDATE_HOL map.lookup entry
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨entry.1 :: keys, ?_⟩
    intro key hlookup
    simp only [FUPDATE_HOL] at hlookup
    by_cases h : key = entry.1
    · subst h
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply hkeys
      simpa [h] using hlookup

/-- HOL `FUPDATE_LIST` (`|++`) on the finite-support carrier using `DecidableEq`
    (HOL `=`), mirroring `updateList` with the equality-based `FUPDATE_HOL`. -/
def updateListEq [DecidableEq α] (map : HolFiniteMapExact α β)
    (entries : List (α × β)) : HolFiniteMapExact α β where
  lookup := FUPDATE_LIST_HOL map.lookup entries
  finiteSupport := by
    induction entries generalizing map with
    | nil => simpa [FUPDATE_LIST_HOL] using map.finiteSupport
    | cons entry entries ih =>
      simpa [FUPDATE_LIST_HOL_cons, updateEq] using ih (updateEq map entry)

/-- HOL-equality (`=`) domain subtraction on the finite-support carrier. -/
def eraseEq [DecidableEq α] (map : HolFiniteMapExact α β) (key : α) :
    HolFiniteMapExact α β where
  lookup := FDOMSUB_HOL map.lookup key
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨keys, ?_⟩
    intro k hk
    apply hkeys k
    by_cases h : k = key
    · simp [FDOMSUB_HOL, h] at hk
    · simpa [FDOMSUB_HOL, h] using hk

end HolFiniteMapExact

namespace HolFiniteMapExact

@[simp] theorem lookup_updateListEq [DecidableEq α] (map : HolFiniteMapExact α β)
    (entries : List (α × β)) (key : α) :
    (updateListEq map entries).lookup key = FUPDATE_LIST_HOL map.lookup entries key := rfl


end HolFiniteMapExact
end Flapjack
