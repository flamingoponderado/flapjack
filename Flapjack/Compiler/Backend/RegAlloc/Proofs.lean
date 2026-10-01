import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Misc.SptreeLookup

/-!
# reg_alloc proofs

Counterpart of `cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml`.
-/

namespace Flapjack.RegAlloc

/-- Exact HOL `domain_numset_list_delete` (`reg_allocProofScript.sml:1354-1362`):
the domain after deleting a list is the original domain minus the list's
members. HOL sets are predicates and `DIFF` a negated conjunct. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "domain_numset_list_delete"]
theorem domainNumsetListDelete {α : Type} :
    ∀ (l : List Nat) (live : Spt α),
      sptDomain (numsetListDelete l live) = fun k => sptDomain live k ∧ k ∉ l
  | [], live => by funext k; simp [numsetListDelete]
  | x :: xs, live => by
      rw [numsetListDelete, domainNumsetListDelete xs (sptDelete x live)]
      funext k
      apply propext
      unfold sptDomain
      rw [sptLookup_sptDelete]
      by_cases h : k = x <;> simp [h]

/-- Exact HOL `check_partial_col_success` (`reg_allocProofScript.sml:1253-1294`):
when the coloured set is the image of the live set and the colouring is
injective on the checked names together with the live set, the partial check
succeeds and preserves the image invariant. HOL sets are predicates, `IMAGE`
an existential and `INJ _ _ UNIV` scoped injectivity (the `UNIV` codomain
condition is trivial). No well-formedness premise is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "check_partial_col_success"]
theorem checkPartialColSuccess :
    ∀ (ls : List Nat) (live flive : NumSet) (col : Nat → Nat),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ col x = y) ∧
      (∀ x y, (x ∈ ls ∨ sptDomain live x) → (y ∈ ls ∨ sptDomain live y) →
        col x = col y → x = y) →
      ∃ livein flivein,
        checkPartialCol col ls live flive = some (livein, flivein) ∧
        sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ col x = y)
  | [], live, flive, col, ⟨hd, _⟩ => ⟨live, flive, rfl, hd⟩
  | h :: ls, live, flive, col, ⟨hd, hi⟩ => by
      have dins (tree : NumSet) (a x : Nat) :
          sptDomain (sptInsert a () tree) x ↔ x = a ∨ sptDomain tree x :=
        sptMem_sptInsert x a () tree
      have hiTail : ∀ x y, (x ∈ ls ∨ sptDomain live x) → (y ∈ ls ∨ sptDomain live y) →
          col x = col y → x = y := by
        intro x y hx hy he
        refine hi x y ?_ ?_ he
        · rcases hx with hx | hx
          · exact Or.inl (List.mem_cons_of_mem h hx)
          · exact Or.inr hx
        · rcases hy with hy | hy
          · exact Or.inl (List.mem_cons_of_mem h hy)
          · exact Or.inr hy
      cases hl : sptLookup h live with
      | some value =>
          cases value
          obtain ⟨livein, flivein, hc, hd'⟩ := checkPartialColSuccess ls live flive col ⟨hd, hiTail⟩
          exact ⟨livein, flivein, by simpa only [checkPartialCol, hl] using hc, hd'⟩
      | none =>
          have hnl : ¬ sptDomain live h := by simp [sptDomain, hl]
          have hf : sptLookup (col h) flive = none := by
            cases hfl : sptLookup (col h) flive with
            | none => rfl
            | some _ =>
                exfalso
                have hm : sptDomain flive (col h) := by simp [sptDomain, hfl]
                rw [hd] at hm
                obtain ⟨x, hx, he⟩ := hm
                have := hi x h (Or.inr hx) (Or.inl List.mem_cons_self) he
                subst this
                exact hnl hx
          have hd2 : sptDomain (sptInsert (col h) () flive) =
              (fun y => ∃ x, sptDomain (sptInsert h () live) x ∧ col x = y) := by
            funext y
            apply propext
            rw [dins, hd]
            constructor
            · rintro (he | ⟨x, hx, he⟩)
              · exact ⟨h, (dins live h h).mpr (Or.inl rfl), he.symm⟩
              · exact ⟨x, (dins live h x).mpr (Or.inr hx), he⟩
            · rintro ⟨x, hx, he⟩
              rcases (dins live h x).mp hx with hx | hx
              · subst x; exact Or.inl he.symm
              · exact Or.inr ⟨x, hx, he⟩
          have hi2 : ∀ x y, (x ∈ ls ∨ sptDomain (sptInsert h () live) x) →
              (y ∈ ls ∨ sptDomain (sptInsert h () live) y) → col x = col y → x = y := by
            have lift : ∀ z, (z ∈ ls ∨ sptDomain (sptInsert h () live) z) →
                (z ∈ h :: ls ∨ sptDomain live z) := by
              intro z hz
              rcases hz with hz | hz
              · exact Or.inl (List.mem_cons_of_mem h hz)
              · rcases (dins live h z).mp hz with hz | hz
                · subst z; exact Or.inl List.mem_cons_self
                · exact Or.inr hz
            intro x y hx hy he
            exact hi x y (lift x hx) (lift y hy) he
          obtain ⟨livein, flivein, hc, hd'⟩ :=
            checkPartialColSuccess ls (sptInsert h () live) (sptInsert (col h) () flive) col
              ⟨hd2, hi2⟩
          exact ⟨livein, flivein, by simpa only [checkPartialCol, hl, hf] using hc, hd'⟩

/-- Exact HOL `check_partial_col_domain` (`reg_allocProofScript.sml:1541-1550`):
a successful partial check returns the live set extended by the checked
names. `set ls ∪ domain live` is the predicate `x ∈ ls ∨ sptDomain live x`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "check_partial_col_domain"]
theorem checkPartialColDomain :
    ∀ (ls : List Nat) (f : Nat → Nat) (live flive : NumSet) (v : NumSet × NumSet),
      checkPartialCol f ls live flive = some v →
      sptDomain v.1 = (fun x => x ∈ ls ∨ sptDomain live x)
  | [], f, live, flive, v, hc => by
      simp only [checkPartialCol, Option.some.injEq] at hc
      subst hc
      funext x; simp
  | h :: ls, f, live, flive, v, hc => by
      have dins (tree : NumSet) (a x : Nat) :
          sptDomain (sptInsert a () tree) x ↔ x = a ∨ sptDomain tree x :=
        sptMem_sptInsert x a () tree
      cases hl : sptLookup h live with
      | some value =>
          cases value
          have hc' : checkPartialCol f ls live flive = some v := by
            simpa only [checkPartialCol, hl] using hc
          rw [checkPartialColDomain ls f live flive v hc']
          have hm : sptDomain live h := by simp [sptDomain, hl]
          funext x
          apply propext
          constructor
          · rintro (hx | hx)
            · exact Or.inl (List.mem_cons_of_mem h hx)
            · exact Or.inr hx
          · rintro (hx | hx)
            · rcases List.mem_cons.mp hx with hx | hx
              · subst x; exact Or.inr hm
              · exact Or.inl hx
            · exact Or.inr hx
      | none =>
          cases hf : sptLookup (f h) flive with
          | some _ => simp [checkPartialCol, hl, hf] at hc
          | none =>
              have hc' : checkPartialCol f ls (sptInsert h () live)
                  (sptInsert (f h) () flive) = some v := by
                simpa only [checkPartialCol, hl, hf] using hc
              rw [checkPartialColDomain ls f _ _ v hc']
              funext x
              apply propext
              rw [dins]
              constructor
              · rintro (hx | hx | hx)
                · exact Or.inl (List.mem_cons_of_mem h hx)
                · subst x; exact Or.inl List.mem_cons_self
                · exact Or.inr hx
              · rintro (hx | hx)
                · rcases List.mem_cons.mp hx with hx | hx
                  · exact Or.inr (Or.inl hx)
                  · exact Or.inl hx
                · exact Or.inr (Or.inr hx)

end Flapjack.RegAlloc
