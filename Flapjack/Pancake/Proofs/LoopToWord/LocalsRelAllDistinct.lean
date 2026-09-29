import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelUpdates

/-!
# Exact Loop-to-Word distinctness of mapped context variables

Ports `loop_to_wordProof$locals_rel_ALL_DISTINCT_MAP` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:234-240`.  The context and
the two local environments are the exact `Spt` (`sptree$num_map`) carrier, the
local values the exact width-indexed `WordLocW` carrier, and the source list a
plain HOL list rendered by constructor-for-constructor Lean `List`.  HOL's
`set xs SUBSET domain ctxt` is rendered pointwise as
`∀ name, name ∈ xs → sptMem name context`, matching the sibling renderings used
by the `locals_rel` update lemmas.
-/

namespace Flapjack.LoopToWord

/-- Exact HOL `loop_to_wordProof$locals_rel_ALL_DISTINCT_MAP`: the mapped
registers of a distinct source list that lies inside the context domain are
themselves distinct, using the injectivity clause of `localsRelHOL`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml"
  "locals_rel_ALL_DISTINCT_MAP" (words_as_type_indexed_bitvec)]
theorem localsRelHOLAllDistinctMap {width : Nat} [NeZero width]
    (context : Spt Nat) (sourceLocals targetLocals : Spt (WordLocW width))
    (xs : List Nat)
    (hpremises : localsRelHOL context sourceLocals targetLocals ∧
      (∀ name, name ∈ xs → sptMem name context) ∧
      xs.Nodup) :
    (xs.map (findVarHOL context)).Nodup := by
  rcases hpremises with ⟨hrel, hsubset, hnodup⟩
  rcases hrel with ⟨hinjective, _heven, _hsim⟩
  have hmap : ∀ names : List Nat,
      (∀ name, name ∈ names → sptMem name context) → names.Nodup →
      (names.map (findVarHOL context)).Nodup := by
    intro names
    induction names with
    | nil => intro _ _; simp
    | cons name names ih =>
        intro hmemAll hnames
        have hnames' := List.nodup_cons.mp hnames
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          rcases List.mem_map.mp hmem with ⟨other, hother, heq⟩
          have hmemName : sptMem name context := hmemAll name (by simp)
          have hmemOther : sptMem other context := hmemAll other (by simp [hother])
          have heq' : findVarHOL context name = findVarHOL context other := heq.symm
          have hotherName : name = other :=
            hinjective name other hmemName hmemOther heq'
          apply hnames'.1
          rw [hotherName]
          exact hother
        · exact ih (fun a ha => hmemAll a (by simp [ha])) hnames'.2
  exact hmap xs hsubset hnodup

end Flapjack.LoopToWord
