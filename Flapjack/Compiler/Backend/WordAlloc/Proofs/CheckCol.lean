import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSets
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

namespace Flapjack.WordAlloc

/-- Literal fixed-set checker soundness: successful checking retains the input
tree, proves injection on its entire domain, and identifies the entire output
domain with its image. No wf premise or global injection assumption is added. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "check_col_INJ"]
theorem checkColInj (f : Nat → Nat) (tree q r : NumSet)
    (h : RegAlloc.checkCol f tree = some (q, r)) :
    q = tree ∧
      (∀ x y, sptDomain q x → sptDomain q y → f x = f y → x = y) ∧
      sptDomain r = (fun y => ∃ x, sptDomain q x ∧ f x = y) := by
  let keys := (sptToAList tree).map Prod.fst
  have hdomain (key : Nat) : sptDomain tree key ↔ sptLookup key tree = some () := by
    cases hv : sptLookup key tree with
    | none => simp [sptDomain, hv]
    | some value => cases value; simp [sptDomain, hv]
  have hkeys (key : Nat) : key ∈ keys ↔ sptDomain tree key := by
    constructor
    · intro hm
      have hm' : ∃ entry : Nat × Unit,
          entry ∈ sptToAList tree ∧ entry.1 = key := List.mem_map.mp hm
      obtain ⟨⟨name, value⟩, hentry, he⟩ := hm'
      cases value
      subst key
      exact (hdomain name).mpr ((sptToAList_mem_iff_lookup tree name ()).mp hentry)
    · intro hd
      exact List.mem_map.mpr ⟨(key, ()),
        (sptToAList_mem_iff_lookup tree key ()).mpr ((hdomain key).mp hd), rfl⟩
  have hfrom (names : List Nat) :
      sptFromAList (names.map (fun name => (name, ()))) = numsetListInsert names .ln := by
    induction names with
    | nil => rfl
    | cons name names ih => simp only [List.map_cons, sptFromAList, numsetListInsert, ih]
  have hcol : RegAlloc.checkCol f tree =
      if (keys.map f).Pairwise (· ≠ ·) then
        some (tree, numsetListInsert (keys.map f) .ln) else none := by
    simp only [RegAlloc.checkCol, hfrom]
    simp only [keys, List.map_map, Function.comp_def]
  rw [hcol] at h
  split at h
  · rename_i hd
    have hp := Option.some.inj h
    have hq := congrArg Prod.fst hp
    have hr := congrArg Prod.snd hp
    dsimp at hq hr
    subst q
    subst r
    refine ⟨rfl, ?_, ?_⟩
    · have hinj : ∀ (names : List Nat), (names.map f).Pairwise (· ≠ ·) →
          ∀ x y, x ∈ names → y ∈ names → f x = f y → x = y := by
        intro names
        induction names with
        | nil => intro _ x y hx; simp at hx
        | cons name names ih =>
          intro hdist x y hx hy he
          have hh := List.pairwise_cons.mp hdist
          rcases List.mem_cons.mp hx with hx | hx
          · subst x
            rcases List.mem_cons.mp hy with hy | hy
            · exact hy.symm
            · exact False.elim (hh.1 (f y) (List.mem_map_of_mem hy) he)
          · rcases List.mem_cons.mp hy with hy | hy
            · subst y
              exact False.elim (hh.1 (f x) (List.mem_map_of_mem hx) he.symm)
            · exact ih hh.2 x y hx hy he
      intro x y hx hy he
      exact hinj keys hd x y ((hkeys x).mpr hx) ((hkeys y).mpr hy) he
    · rw [domainNumsetListInsert]
      funext y
      apply propext
      simp only [sptDomain, sptLookup, Option.isSome_none, Bool.false_eq_true,
        false_or, List.mem_map]
      constructor
      · rintro ⟨x, hx, he⟩
        exact ⟨x, (hkeys x).mp hx, he⟩
      · rintro ⟨x, hx, he⟩
        exact ⟨x, (hkeys x).mpr hx, he⟩
  · simp at h

end Flapjack.WordAlloc
