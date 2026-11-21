module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Removal.LeafLocs
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallCode

@[expose] public section

/-!
# `word_removal_lemma`: the statement for one program and state

`WordRemovalGoal program state` is the conclusion of HOL `word_removal_lemma`
(`word_elimProofScript.sml:931-944`) for fixed `program` and `state`, with every
other variable universally quantified in HOL's order.  The case pieces of
`word_removal_lemma` are stated with it, and the assembling theorem states the
HOL theorem in full.  HOL's `no_install p` is the tagged Boolean
`noInstallSubprogsHOL p = true`, `domain A ⊆ domain B` is
`sptDomainSet A ⊆ sptDomainSet B`, and `dest_result_loc result ⊆ domain
reachable` is `{n | destResultLoc result n} ⊆ sptDomainSet reachable`.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps

/-- HOL `word_removal_lemma`'s statement for one program and initial state.
    Flapjack infrastructure for its case split. -/
def WordRemovalGoal {width : Nat} [NeZero width] {C F : Type}
    (program : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F) :
    Prop :=
  ∀ (result : Option (WordSemResult width)) (new_state : WordSemStateFiniteExact width C F)
    (reachable : NumSet) (removed_state : WordSemStateFiniteExact width C F),
    evaluate program state = (result, new_state) ∧ result ≠ some .error ∧
      wordStateRel reachable state removed_state ∧ gcNoNewLocs state.gcFun ∧
      noInstallSubprogsHOL program = true ∧ noInstallCode state.code ∧
      noInstallCode removed_state.code ∧
      sptDomainSet (findWordRef program) ⊆ sptDomainSet reachable ∧
      codeClosed reachable state.code →
    ∃ s, evaluate program removed_state = (result, s) ∧ wordStateRel reachable new_state s ∧
      {n | destResultLoc result n} ⊆ sptDomainSet reachable

section Leaf
variable {width : Nat} [NeZero width] {C F : Type}

/-- The reachable locations of a related original state. -/
theorem wordStateRel_locs {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) :
    ∀ n, sptMem n (findLocState s) → sptMem n reachable :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- A leaf statement whose successful runs add no location satisfies the
    removal statement. Flapjack infrastructure. -/
theorem removal_leaf (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (hp : removalLeaf p = true)
    (hloc : ∀ res s1, evaluate p s = (res, s1) → res ≠ some .error → gcNoNewLocs s.gcFun →
      LocsWithin s1 s ∧ ∀ n, destResultLoc res n → sptMem n (findLocState s)) :
    WordRemovalGoal p s := by
  intro result new_state reachable removed ⟨hev, herr, hrel, hg, hni, hnic, _, _, _⟩
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode hrel
  obtain ⟨hl, hr⟩ := hloc result new_state hev herr hg
  have hcode : new_state.code = s.code := by
    have := code_evaluate p s hni hnic
    rw [hev] at this
    exact this
  refine ⟨{ new_state with code := c }, by rw [evaluate_withCode_leaf c s p hp, hev], ?_, ?_⟩
  · exact wordStateRel_withCode_within hrel hcode hl
  · intro n hn
    exact wordStateRel_locs hrel n (hr n hn)

end Leaf

end Flapjack.Compiler.Backend.WordElim
