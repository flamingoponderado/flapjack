import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSetInsertion
import Flapjack.Misc.Sptree.InsertUnchanged

namespace Flapjack.WordAlloc

/-- Successful partial checking preserves wf, returns literal list insertion,
and establishes scoped injection and the entire colour-domain image.
Only the original input invariants and checker-success premise are required. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "check_partial_col_INJ"]
theorem checkPartialColInj (names : List Nat) (f : Nat → Nat)
    (live coloured live' coloured' : NumSet)
    (hw : sptWf live = true)
    (hd : sptDomain coloured = (fun y => ∃ x, sptDomain live x ∧ f x = y))
    (hi : ∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y)
    (hc : RegAlloc.checkPartialCol f names live coloured = some (live', coloured')) :
    sptWf live' = true ∧ live' = numsetListInsert names live ∧
      (∀ x y, sptDomain live' x → sptDomain live' y → f x = f y → x = y) ∧
      sptDomain coloured' = (fun y => ∃ x, sptDomain live' x ∧ f x = y) := by
  have dins (tree : NumSet) (a x : Nat) :
      sptDomain (sptInsert a () tree) x ↔ x = a ∨ sptDomain tree x := by
    exact sptMem_sptInsert x a () tree
  induction names generalizing live coloured live' coloured' with
  | nil =>
      have hp := Option.some.inj hc
      cases hp
      exact ⟨hw, rfl, hi, hd⟩
  | cons name names ih =>
      cases hl : sptLookup name live with
      | some value =>
          cases value
          have hc' : RegAlloc.checkPartialCol f names live coloured =
              some (live', coloured') := by
            simpa only [RegAlloc.checkPartialCol, hl] using hc
          obtain ⟨hw', he, hi', hd'⟩ := ih live coloured live' coloured' hw hd hi hc'
          refine ⟨hw', ?_, hi', hd'⟩
          rw [he, numsetListInsert, ← (numsetListInsertSwap names name live hw).2,
            sptInsertUnchanged live name () hl]
      | none =>
          cases hf : sptLookup (f name) coloured with
          | some value => simp [RegAlloc.checkPartialCol, hl, hf] at hc
          | none =>
              have hn : ¬ sptDomain coloured (f name) := by simp [sptDomain, hf]
              have hcollision (x : Nat) (hx : sptDomain live x) : f x ≠ f name := by
                intro he
                apply hn
                rw [hd]
                exact ⟨x, hx, he⟩
              have hi2 : ∀ x y, sptDomain (sptInsert name () live) x →
                  sptDomain (sptInsert name () live) y → f x = f y → x = y := by
                intro x y hx hy he
                rcases (dins live name x).mp hx with hx | hx
                · subst x
                  rcases (dins live name y).mp hy with hy | hy
                  · exact hy.symm
                  · exact False.elim (hcollision y hy he.symm)
                · rcases (dins live name y).mp hy with hy | hy
                  · subst y; exact False.elim (hcollision x hx he)
                  · exact hi x y hx hy he
              have hd2 : sptDomain (sptInsert (f name) () coloured) =
                  (fun y => ∃ x, sptDomain (sptInsert name () live) x ∧ f x = y) := by
                funext y
                apply propext
                rw [dins, hd]
                constructor
                · rintro (he | ⟨x, hx, he⟩)
                  · exact ⟨name, (dins live name name).mpr (Or.inl rfl), he.symm⟩
                  · exact ⟨x, (dins live name x).mpr (Or.inr hx), he⟩
                · rintro ⟨x, hx, he⟩
                  rcases (dins live name x).mp hx with hx | hx
                  · subst x; exact Or.inl he.symm
                  · exact Or.inr ⟨x, hx, he⟩
              have hc' : RegAlloc.checkPartialCol f names (sptInsert name () live)
                  (sptInsert (f name) () coloured) = some (live', coloured') := by
                simpa only [RegAlloc.checkPartialCol, hl, hf] using hc
              obtain ⟨hw', he, hi', hd'⟩ := ih _ _ _ _
                (sptWfInsert name () live hw) hd2 hi2 hc'
              refine ⟨hw', ?_, hi', hd'⟩
              rw [he, numsetListInsert, (numsetListInsertSwap names name live hw).2]

end Flapjack.WordAlloc
