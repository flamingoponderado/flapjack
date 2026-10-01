import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Remap
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
import Flapjack.Misc.Sptree.Wf

/-!
# reg_alloc `mk_bij` domain, bijection and well-formedness

The `list_remap`/`mk_bij_aux` lemmas of `reg_allocProofScript.sml:802-982`.
HOL `domain t = S` is the predicate equality `sptDomain t = S`; HOL `count n`
is `fun x => x < n`. HOL `Abbrev P` is `P` (`markerTheory.Abbrev_def`).
-/

namespace Flapjack.RegAlloc

/-- Domain of an insertion (Flapjack infrastructure). -/
private theorem domainInsert (k v : Nat) (t : Spt Nat) (x : Nat) :
    sptDomain (sptInsert k v t) x ↔ x = k ∨ sptDomain t x := by
  unfold sptDomain
  by_cases h : x = k
  · subst h; simp [sptLookup_sptInsert_same]
  · simp [sptLookup_sptInsert_ne _ _ _ _ h, h]

/-- Keys of `toAList` are the domain (HOL `toAList_domain`; Flapjack
infrastructure). -/
private theorem toAListKeysDomain (t : NumSet) (k : Nat) :
    k ∈ (sptToAList t).map Prod.fst ↔ sptDomain t k := by
  simp only [List.mem_map, sptDomain]
  constructor
  · rintro ⟨⟨a, v⟩, hm, rfl⟩
    simp [(sptToAList_mem_iff_lookup t a v).mp hm]
  · intro h
    cases hk : sptLookup k t with
    | none => simp [hk] at h
    | some v => exact ⟨(k, v), (sptToAList_mem_iff_lookup t k v).mpr hk, rfl⟩

/-- HOL `list_remap_domain` (`reg_allocProofScript.sml:802-812`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "list_remap_domain"]
theorem listRemapDomain : ∀ (ls : List Nat) (ta fa : Spt Nat) (n : Nat) (ta' fa' : Spt Nat)
    (n' : Nat), listRemap ls (ta, fa, n) = (ta', fa', n') →
      sptDomain ta' = fun x => sptDomain ta x ∨ x ∈ ls := by
  intro ls
  induction ls with
  | nil =>
      intro ta fa n ta' fa' n' h
      simp only [listRemap, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      funext x; simp
  | cons name names ih =>
      intro ta fa n ta' fa' n' h
      simp only [listRemap] at h
      cases hl : sptLookup name ta with
      | some v =>
          rw [hl] at h
          rw [ih ta fa n ta' fa' n' h]
          funext x
          apply propext
          by_cases hx : x = name
          · subst hx; simp [sptDomain, hl]
          · simp [hx]
      | none =>
          rw [hl] at h
          rw [ih _ _ _ ta' fa' n' h]
          funext x
          apply propext
          rw [domainInsert]
          simp only [List.mem_cons]
          constructor
          · rintro ((h1 | h1) | h1)
            · exact Or.inr (Or.inl h1)
            · exact Or.inl h1
            · exact Or.inr (Or.inr h1)
          · rintro (h1 | h1 | h1)
            · exact Or.inl (Or.inr h1)
            · exact Or.inl (Or.inl h1)
            · exact Or.inr h1

/-- HOL `list_remap_bij` (`reg_allocProofScript.sml:814-835`), a `val Q.prove`
without a theory name, so untagged: remapping preserves the inverse pair and the
`count n` domain of the inverse map. -/
theorem listRemapBij : ∀ (ls : List Nat) (ta fa : Spt Nat) (n : Nat) (ta' fa' : Spt Nat)
    (n' : Nat), listRemap ls (ta, fa, n) = (ta', fa', n') ∧ spInverts ta fa ∧
      spInverts fa ta ∧ sptDomain fa = (fun x => x < n) →
      spInverts ta' fa' ∧ spInverts fa' ta' ∧ sptDomain fa' = (fun x => x < n') := by
  intro ls
  induction ls with
  | nil =>
      rintro ta fa n ta' fa' n' ⟨h, h1, h2, h3⟩
      simp only [listRemap, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨h1, h2, h3⟩
  | cons name names ih =>
      rintro ta fa n ta' fa' n' ⟨h, h1, h2, h3⟩
      simp only [listRemap] at h
      cases hl : sptLookup name ta with
      | some v =>
          rw [hl] at h
          exact ih ta fa n ta' fa' n' ⟨h, h1, h2, h3⟩
      | none =>
          rw [hl] at h
          have hnf : ¬ sptDomain fa n := by rw [h3]; omega
          have hnt : ¬ sptDomain ta name := by simp [sptDomain, hl]
          refine ih _ _ _ ta' fa' n' ⟨h, spInvertsInsert ta fa name n ⟨h1, hnt, hnf⟩,
            spInvertsInsert fa ta n name ⟨h2, hnf, hnt⟩, ?_⟩
          funext x
          apply propext
          rw [domainInsert, h3]
          omega

/-- HOL `mk_bij_aux_domain` (`reg_allocProofScript.sml:837-877`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_bij_aux_domain"]
theorem mkBijAuxDomain : ∀ (ct : ClashTree) (ta fa : Spt Nat) (n : Nat) (ta' fa' : Spt Nat)
    (n' : Nat), mkBijAux ct (ta, fa, n) = (ta', fa', n') →
      sptDomain ta' = fun x => sptDomain ta x ∨ inClashTree ct x := by
  intro ct
  induction ct with
  | delta w r =>
      intro ta fa n ta' fa' n' h
      simp only [mkBijAux] at h
      rcases hr : listRemap r (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rw [hr] at h
      rw [listRemapDomain w ta1 fa1 n1 ta' fa' n' h, listRemapDomain r ta fa n ta1 fa1 n1 hr]
      funext x
      apply propext
      simp only [inClashTree]
      constructor
      · rintro ((h1 | h1) | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
        · exact Or.inr (Or.inl h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inr h1
        · exact Or.inl (Or.inr h1)
  | set t =>
      intro ta fa n ta' fa' n' h
      simp only [mkBijAux] at h
      rw [listRemapDomain _ ta fa n ta' fa' n' h]
      funext x
      simp only [inClashTree, toAListKeysDomain]
  | branch fixed left right ihl ihr =>
      intro ta fa n ta' fa' n' h
      simp only [mkBijAux] at h
      rcases h1 : mkBijAux left (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rcases h2 : mkBijAux right (ta1, fa1, n1) with ⟨ta2, fa2, n2⟩
      rw [h1] at h
      simp only [h2] at h
      have d1 := ihl ta fa n ta1 fa1 n1 h1
      have d2 := ihr ta1 fa1 n1 ta2 fa2 n2 h2
      cases fixed with
      | none =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, -, -⟩ := h
          rw [d2, d1]
          funext x
          apply propext
          simp only [inClashTree, or_false]
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          · rintro (h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
      | some t =>
          simp only at h
          rw [listRemapDomain _ ta2 fa2 n2 ta' fa' n' h, d2, d1]
          funext x
          apply propext
          simp only [inClashTree, toAListKeysDomain]
          constructor
          · rintro (((h | h) | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
          · rintro (h | h | h | h)
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
  | seq left right ihl ihr =>
      intro ta fa n ta' fa' n' h
      simp only [mkBijAux] at h
      rcases h1 : mkBijAux right (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rw [h1] at h
      rw [ihl ta1 fa1 n1 ta' fa' n' h, ihr ta fa n ta1 fa1 n1 h1]
      funext x
      apply propext
      simp only [inClashTree]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)

/-- HOL `mk_bij_aux_bij` (`reg_allocProofScript.sml:879-919`), a `val Q.prove`
without a theory name, so untagged. -/
theorem mkBijAuxBij : ∀ (ct : ClashTree) (ta fa : Spt Nat) (n : Nat) (ta' fa' : Spt Nat)
    (n' : Nat), mkBijAux ct (ta, fa, n) = (ta', fa', n') ∧ spInverts ta fa ∧
      spInverts fa ta ∧ sptDomain fa = (fun x => x < n) →
      spInverts ta' fa' ∧ spInverts fa' ta' ∧ sptDomain fa' = (fun x => x < n') := by
  intro ct
  induction ct with
  | delta w r =>
      rintro ta fa n ta' fa' n' ⟨h, hb⟩
      simp only [mkBijAux] at h
      rcases hr : listRemap r (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rw [hr] at h
      exact listRemapBij w ta1 fa1 n1 ta' fa' n' ⟨h, listRemapBij r ta fa n ta1 fa1 n1 ⟨hr, hb⟩⟩
  | set t =>
      rintro ta fa n ta' fa' n' ⟨h, hb⟩
      simp only [mkBijAux] at h
      exact listRemapBij _ ta fa n ta' fa' n' ⟨h, hb⟩
  | branch fixed left right ihl ihr =>
      rintro ta fa n ta' fa' n' ⟨h, hb⟩
      simp only [mkBijAux] at h
      rcases h1 : mkBijAux left (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rcases h2 : mkBijAux right (ta1, fa1, n1) with ⟨ta2, fa2, n2⟩
      rw [h1] at h
      simp only [h2] at h
      have b2 := ihr ta1 fa1 n1 ta2 fa2 n2 ⟨h2, ihl ta fa n ta1 fa1 n1 ⟨h1, hb⟩⟩
      cases fixed with
      | none =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact b2
      | some t =>
          simp only at h
          exact listRemapBij _ ta2 fa2 n2 ta' fa' n' ⟨h, b2⟩
  | seq left right ihl ihr =>
      rintro ta fa n ta' fa' n' ⟨h, hb⟩
      simp only [mkBijAux] at h
      rcases h1 : mkBijAux right (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rw [h1] at h
      exact ihl ta1 fa1 n1 ta' fa' n' ⟨h, ihr ta fa n ta1 fa1 n1 ⟨h1, hb⟩⟩

/-- HOL `list_remap_wf` (`reg_allocProofScript.sml:921-933`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "list_remap_wf"]
theorem listRemapWf : ∀ (l : List Nat) (ta fa : Spt Nat) (n : Nat) (ta' fa' : Spt Nat)
    (n' : Nat), listRemap l (ta, fa, n) = (ta', fa', n') ∧ sptWf ta = true ∧ sptWf fa = true →
      sptWf ta' = true ∧ sptWf fa' = true := by
  intro l
  induction l with
  | nil =>
      rintro ta fa n ta' fa' n' ⟨h, h1, h2⟩
      simp only [listRemap, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨h1, h2⟩
  | cons name names ih =>
      rintro ta fa n ta' fa' n' ⟨h, h1, h2⟩
      simp only [listRemap] at h
      cases hl : sptLookup name ta with
      | some v =>
          rw [hl] at h
          exact ih ta fa n ta' fa' n' ⟨h, h1, h2⟩
      | none =>
          rw [hl] at h
          exact ih _ _ _ ta' fa' n' ⟨h, sptWfInsert _ _ _ h1, sptWfInsert _ _ _ h2⟩

/-- HOL `mk_bij_aux_wf` (`reg_allocProofScript.sml:935-982`); HOL's
`Abbrev (wf ta' ∧ wf fa')` is the plain conjunction. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_bij_aux_wf"]
theorem mkBijAuxWf : ∀ (ct : ClashTree) (ta fa : Spt Nat) (n : Nat) (ta' fa' : Spt Nat)
    (n' : Nat), mkBijAux ct (ta, fa, n) = (ta', fa', n') ∧ sptWf ta = true ∧ sptWf fa = true →
      sptWf ta' = true ∧ sptWf fa' = true := by
  intro ct
  induction ct with
  | delta w r =>
      rintro ta fa n ta' fa' n' ⟨h, hw⟩
      simp only [mkBijAux] at h
      rcases hr : listRemap r (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rw [hr] at h
      exact listRemapWf w ta1 fa1 n1 ta' fa' n' ⟨h, listRemapWf r ta fa n ta1 fa1 n1 ⟨hr, hw⟩⟩
  | set t =>
      rintro ta fa n ta' fa' n' ⟨h, hw⟩
      simp only [mkBijAux] at h
      exact listRemapWf _ ta fa n ta' fa' n' ⟨h, hw⟩
  | branch fixed left right ihl ihr =>
      rintro ta fa n ta' fa' n' ⟨h, hw⟩
      simp only [mkBijAux] at h
      rcases h1 : mkBijAux left (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rcases h2 : mkBijAux right (ta1, fa1, n1) with ⟨ta2, fa2, n2⟩
      rw [h1] at h
      simp only [h2] at h
      have w2 := ihr ta1 fa1 n1 ta2 fa2 n2 ⟨h2, ihl ta fa n ta1 fa1 n1 ⟨h1, hw⟩⟩
      cases fixed with
      | none =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact w2
      | some t =>
          simp only at h
          exact listRemapWf _ ta2 fa2 n2 ta' fa' n' ⟨h, w2⟩
  | seq left right ihl ihr =>
      rintro ta fa n ta' fa' n' ⟨h, hw⟩
      simp only [mkBijAux] at h
      rcases h1 : mkBijAux right (ta, fa, n) with ⟨ta1, fa1, n1⟩
      rw [h1] at h
      exact ihl ta1 fa1 n1 ta' fa' n' ⟨h, ihr ta fa n ta1 fa1 n1 ⟨h1, hw⟩⟩

end Flapjack.RegAlloc
