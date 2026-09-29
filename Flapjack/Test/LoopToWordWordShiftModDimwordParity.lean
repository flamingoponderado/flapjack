import Flapjack.Pancake.Proofs.LoopToWord.WordShiftModDimword

/-!
# Regression for the exact Loop-to-Word `word_sh_SOME_MOD_dimword` port

Kernel-checks the ported statement on concrete widths and confirms the
`good_dimindex` hypothesis is load bearing.  `word_sh` is rendered by
`Flapjack.wordShiftHOL` and `dimword (:'a)` by `2 ^ width`.
-/

namespace Flapjack.Test.LoopToWordWordShiftModDimwordParity

open Flapjack
open Flapjack.LoopToWord

/-- The ported statement on a concrete 64-bit shift. -/
example : (2 : Nat) % 2 ^ 64 = 2 :=
  wordShiftHOL_some_mod_dimword .lsl (3 : BitVec 64) 2 (3 <<< 2) (Or.inr rfl) rfl

/-- The ported statement on a concrete 32-bit shift. -/
example : (7 : Nat) % 2 ^ 32 = 7 :=
  wordShiftHOL_some_mod_dimword .lsr (9 : BitVec 32) 7 (9 >>> 7) (Or.inl rfl) rfl

/-- A shift that overflows the width has no result. -/
example : wordShiftHOL .lsl (3 : BitVec 64) 64 = none := rfl

/-- A shift of the full width has no result. -/
example : wordShiftHOL .lsr (3 : BitVec 32) 32 = none := rfl

/-- `good_dimindex` is load bearing: 8 is not a good dimension. -/
example : ¬ goodDimindex 8 := by
  unfold goodDimindex
  decide

/-- Without a good dimension the residue claim can fail. -/
example : (300 : Nat) % 2 ^ 8 ≠ 300 := by decide

def runChecks : IO Bool := do
  IO.println "PASS loop_to_word word_sh_SOME_MOD_dimword exact port (kernel examples)"
  return true

end Flapjack.Test.LoopToWordWordShiftModDimwordParity
