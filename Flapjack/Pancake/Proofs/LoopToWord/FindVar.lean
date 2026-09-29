import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel

/-!
# Exact Loop-to-Word `find_var` side lemmas

Ports `loop_to_wordProof$find_var_neq_0` and
`loop_to_wordProof$find_var_neq_odd` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:169-194`.  Both are exact
statements about `find_var` on the reviewed `locals_rel` context: the context
and the two local environments use the exact `Spt` (`sptree$num_map`) carrier,
the local values the exact width-indexed `WordLocW` carrier (used only by
`find_var_neq_0`'s relation premise), and `find_var` the exact `findVarHOL`.
HOL's `EVEN m` is `m % 2 = 0`; `find_var_neq_odd` mentions no word carrier, so
its tag is unqualified.
-/

namespace Flapjack.LoopToWord

/-- Exact HOL `loop_to_wordProof$find_var_neq_0`: a context variable in the
domain of a `locals_rel` context is mapped to a nonzero register. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "find_var_neq_0"
  (words_as_type_indexed_bitvec)]
theorem findVarHOL_ne_zero {width : Nat} [NeZero width]
    (context : Spt Nat) (sourceLocals targetLocals : Spt (WordLocW width))
    (v : Nat)
    (hpremises : sptMem v context ∧ localsRelHOL context sourceLocals targetLocals) :
    findVarHOL context v ≠ 0 := by
  rcases hpremises with ⟨hmem, hrel⟩
  rcases hrel with ⟨_hinjective, heven, _hsim⟩
  obtain ⟨register, hlookup⟩ := (sptMem_iff_lookup v context).mp hmem
  have h := heven v register hlookup
  simp only [findVarHOL]
  rw [hlookup]
  exact h.1

/-- Exact HOL `loop_to_wordProof$find_var_neq_odd`: under an even-only context
assignment, `find_var` never returns an odd register. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "find_var_neq_odd"]
theorem findVarHOL_ne_odd {width : Nat} [NeZero width]
    (context : Spt Nat) (v k : Nat)
    (hpremises : (∀ n m, sptLookup n context = some m → m ≠ 0 ∧ m % 2 = 0) ∧
      k % 2 ≠ 0) :
    findVarHOL context v ≠ k := by
  rcases hpremises with ⟨heven, hk⟩
  simp only [findVarHOL]
  cases hlookup : sptLookup v context with
  | none =>
      intro h
      exact hk (by rw [← h]; decide)
  | some m =>
      simp only [Option.getD_some]
      intro heq
      have hm := heven v m hlookup
      exact hk (by rw [← heq]; exact hm.2)

end Flapjack.LoopToWord
