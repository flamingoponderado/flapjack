import Flapjack.Pancake.WordLang
import Flapjack.Misc.GoodDimindex

namespace Flapjack.LoopToWord

/-- Exact port of HOL `loop_to_wordProofScript.sml:453-458` `word_sh_SOME_MOD_dimword`
(`good_dimindex (:'a) /\ word_sh sh (w : 'a word) n = SOME z ==> n MOD dimword (:'a) = n`).

The HOL type dimension `dimindex (:'a)` is rendered as the positive Lean width `width`
(`BitVec width`), and HOL `dimword (:'a) = 2 ** dimindex (:'a)` as `2 ^ width`; the
`good_dimindex` hypothesis is the tagged `Flapjack.goodDimindex` (`width = 32 \/ width = 64`,
`Flapjack/Misc/GoodDimindex.lean:27`, tag `good_dimindex_def`), and HOL `word_sh` is the tagged
`Flapjack.wordShiftHOL` (`Flapjack/Pancake/WordLang.lean:46`, tag `word_sh_def`). The shift
returns `some` exactly when the amount does not overflow the width, which forces `n = 0` or
`n < width`, so the residue is the amount itself. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "word_sh_SOME_MOD_dimword"
  (words_as_type_indexed_bitvec)]
theorem wordShiftHOL_some_mod_dimword {width : Nat} [NeZero width]
    (sh : Shift) (w : BitVec width) (n : Nat) (z : BitVec width)
    (hgd : goodDimindex width) (h : wordShiftHOL sh w n = some z) :
    n % 2 ^ width = n := by
  unfold wordShiftHOL at h
  by_cases hbad : n ≠ 0 ∧ width ≤ n
  · rw [if_pos hbad] at h
    exact absurd h (by simp)
  · rw [if_neg hbad] at h
    by_cases hzero : n = 0
    · subst hzero
      simp
    · have hlt : n < width := by
        cases Nat.lt_or_ge n width with
        | inl h => exact h
        | inr h => exact absurd ⟨hzero, h⟩ hbad
      rcases hgd with h32 | h64
      · subst h32
        omega
      · subst h64
        omega

end Flapjack.LoopToWord
