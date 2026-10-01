import Flapjack.HolRef
import Flapjack.Misc.Sptree.Wf

/-!
# HOL sptree `toAList` and `domain` library theorems

Ports of the HOL4 `sptreeScript.sml` facts about `toAList` membership and key
distinctness, and of the `domain` equations for `insert`, `difference` and
`fromAList`, over the exact `Spt` carrier. HOL sets are predicates:
`k INSERT s` is `fun x => x = k ∨ s x`, `DIFF` a negated conjunct and
`set (MAP FST ls)` list membership. No well-formedness premise is added.
-/

namespace Flapjack

/-- Exact HOL `MEM_toAList` (`sptreeScript.sml:920-926`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "MEM_toAList"]
theorem sptMemToAList {α : Type} :
    ∀ (t : Spt α) (k : Nat) (v : α), (k, v) ∈ sptToAList t ↔ sptLookup k t = some v := by
  intro tree key value
  constructor
  · intro hmem
    have hfold :
        (key, value) ∈ sptFoldi (fun k v entries => (k, v) :: entries) 0 [] tree := by
      simpa [sptToAList] using hmem
    rcases sptFoldi_mem_address tree 0 [] key value hfold with hacc |
      ⟨localKey, haddr, hlookup⟩
    · simp at hacc
    · have hkey : key = localKey := by
        simpa [sptAcc_eq, lrNext] using haddr
      subst localKey
      exact hlookup
  · intro hlookup
    have hfold := sptFoldi_lookup_mem tree 0 [] key value hlookup
    simpa [sptToAList, sptAcc_eq, lrNext] using hfold

private theorem sptAccZero (index : Nat) : sptAcc index 0 = index := by
  rw [sptAcc_eq]; simp

private theorem sptFoldiEmitted {α : Type} (tree : Spt α) :
    ∀ (index : Nat) (acc : List (Nat × α)),
      ∃ emitted, sptFoldi (fun k v entries => (k, v) :: entries) index acc tree =
          emitted ++ acc ∧ (emitted.map Prod.fst).Nodup ∧
          ∀ p ∈ emitted, ∃ k, p.1 = sptAcc index k := by
  induction tree with
  | ln => intro index acc; exact ⟨[], by simp [sptFoldi], by simp, by simp⟩
  | ls v =>
      intro index acc
      exact ⟨[(index, v)], by simp [sptFoldi], by simp,
        by intro p hp; simp at hp; subst hp; exact ⟨0, (sptAccZero index).symm⟩⟩
  | bn left right ihl ihr =>
      intro index acc
      obtain ⟨el, hl, hlnd, hlk⟩ := ihl (index + 2 * lrNext index) acc
      obtain ⟨er, hr, hrnd, hrk⟩ := ihr (index + lrNext index) (el ++ acc)
      refine ⟨er ++ el, ?_, ?_, ?_⟩
      · change sptFoldi _ (index + lrNext index)
          (sptFoldi _ (index + 2 * lrNext index) acc left) right = _
        rw [hl, hr, List.append_assoc]
      · rw [List.map_append, List.nodup_append]
        refine ⟨hrnd, hlnd, ?_⟩
        intro a ha b hb hab
        obtain ⟨pa, hpa, rfl⟩ := List.mem_map.mp ha
        obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
        obtain ⟨ka, hka⟩ := hrk pa hpa
        obtain ⟨kb, hkb⟩ := hlk pb hpb
        rw [hka, hkb, sptAcc_childRight, sptAcc_childLeft] at hab
        have := sptAcc_injective index hab
        omega
      · intro p hp
        rcases List.mem_append.mp hp with h | h
        · obtain ⟨k, hk⟩ := hrk p h; exact ⟨2 * k + 1, by rw [hk, sptAcc_childRight]⟩
        · obtain ⟨k, hk⟩ := hlk p h; exact ⟨2 * k + 2, by rw [hk, sptAcc_childLeft]⟩
  | bs left v right ihl ihr =>
      intro index acc
      obtain ⟨el, hl, hlnd, hlk⟩ := ihl (index + 2 * lrNext index) acc
      obtain ⟨er, hr, hrnd, hrk⟩ := ihr (index + lrNext index) ((index, v) :: (el ++ acc))
      refine ⟨er ++ (index, v) :: el, ?_, ?_, ?_⟩
      · change sptFoldi _ (index + lrNext index)
          ((index, v) :: sptFoldi _ (index + 2 * lrNext index) acc left) right = _
        rw [hl, hr]; simp
      · have hroot : ∀ p ∈ el, p.1 ≠ index := by
          intro p hp heq
          obtain ⟨k, hk⟩ := hlk p hp
          rw [hk, sptAcc_childLeft] at heq
          have := sptAcc_injective index (heq.trans (sptAccZero index).symm)
          omega
        rw [List.map_append, List.nodup_append]
        refine ⟨hrnd, ?_, ?_⟩
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, hlnd⟩
          intro hm
          obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
          exact hroot p hp hpe
        · intro a ha b hb hab
          obtain ⟨pa, hpa, rfl⟩ := List.mem_map.mp ha
          obtain ⟨ka, hka⟩ := hrk pa hpa
          rw [hka, sptAcc_childRight] at hab
          simp only [List.map_cons, List.mem_cons] at hb
          rcases hb with hb | hb
          · rw [hb] at hab
            have := sptAcc_injective index (hab.trans (sptAccZero index).symm)
            omega
          · obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
            obtain ⟨kb, hkb⟩ := hlk pb hpb
            rw [hkb, sptAcc_childLeft] at hab
            have := sptAcc_injective index hab
            omega
      · intro p hp
        simp only [List.mem_append, List.mem_cons] at hp
        rcases hp with h | h | h
        · obtain ⟨k, hk⟩ := hrk p h; exact ⟨2 * k + 1, by rw [hk, sptAcc_childRight]⟩
        · subst h; exact ⟨0, (sptAccZero index).symm⟩
        · obtain ⟨k, hk⟩ := hlk p h; exact ⟨2 * k + 2, by rw [hk, sptAcc_childLeft]⟩

/-- Exact HOL `ALL_DISTINCT_MAP_FST_toAList` (`sptreeScript.sml:1027-1076`);
HOL `ALL_DISTINCT` is `List.Nodup`. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "ALL_DISTINCT_MAP_FST_toAList"]
theorem sptAllDistinctMapFstToAList {α : Type} :
    ∀ (t : Spt α), ((sptToAList t).map Prod.fst).Nodup := by
  intro tree
  obtain ⟨e, he, hnd, -⟩ := sptFoldiEmitted tree 0 []
  simpa [sptToAList, he] using hnd

/-- Exact HOL `domain_insert` (`sptreeScript.sml:658-663`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "domain_insert"]
theorem sptDomainInsert {α : Type} (k : Nat) (v : α) (t : Spt α) :
    sptDomain (sptInsert k v t) = fun x => x = k ∨ sptDomain t x := by
  funext x
  exact propext (sptMem_sptInsert x k v t)

/-- Exact HOL `domain_difference` (`sptreeScript.sml:665-670`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "domain_difference"]
theorem sptDomainDifference {α β : Type} :
    ∀ (t1 : Spt α) (t2 : Spt β),
      sptDomain (sptDifference t1 t2) = fun x => sptDomain t1 x ∧ ¬ sptDomain t2 x := by
  intro t1 t2
  funext x
  unfold sptDomain
  rw [sptLookupDifference]
  cases h1 : sptLookup x t1 <;> cases h2 : sptLookup x t2 <;> simp

/-- Exact HOL `domain_fromAList` (`sptreeScript.sml:1491-1499`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "domain_fromAList"]
theorem sptDomainFromAList {α : Type} :
    ∀ (ls : List (Nat × α)), sptDomain (sptFromAList ls) = fun x => x ∈ ls.map Prod.fst := by
  intro ls
  induction ls with
  | nil => funext x; simp [sptFromAList, sptDomain]
  | cons entry entries ih =>
      obtain ⟨k, v⟩ := entry
      rw [sptFromAList, sptDomainInsert, ih]
      funext x
      simp

/-- Flapjack consequence of `MEM_toAList` used by the allocator proofs:
`set (MAP FST (toAList s)) = domain s`. -/
theorem sptMemMapFstToAList {α : Type} (t : Spt α) (k : Nat) :
    k ∈ (sptToAList t).map Prod.fst ↔ sptDomain t k := by
  simp only [List.mem_map, sptDomain]
  constructor
  · rintro ⟨⟨a, v⟩, hm, rfl⟩
    simp [(sptMemToAList t a v).mp hm]
  · intro h
    cases hl : sptLookup k t with
    | none => simp [hl] at h
    | some v => exact ⟨(k, v), (sptMemToAList t k v).mpr hl, rfl⟩

end Flapjack
