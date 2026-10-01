import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.Compiler.Backend.WordAlloc

@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "is_alloc_var_flip"]
theorem isAllocVarFlip (next : Nat) (h : isAllocVar next) :
    isStackVar (next + 2) := by
  simp [isAllocVar] at h
  simp [isStackVar, Nat.add_mod, h]

@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "is_stack_var_flip"]
theorem isStackVarFlip (next : Nat) (h : isStackVar next) :
    isAllocVar (next + 2) := by
  simp [isStackVar] at h
  simp [isAllocVar, Nat.add_mod, h]

/-- Full source Boolean equalities, including physical-register residues.
There is no allocation-class or stack-class premise for these equalities. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "flip_rw"]
theorem flipRw (next : Nat) :
    isStackVar (next + 2) = isAllocVar next ∧
    isAllocVar (next + 2) = isStackVar next := by
  have h : next % 4 = 0 ∨ next % 4 = 1 ∨ next % 4 = 2 ∨ next % 4 = 3 := by
    have := Nat.mod_lt next (by decide : 0 < 4)
    omega
  rcases h with h | h | h | h <;>
    simp [isStackVar, isAllocVar, Nat.add_mod, h]

end Flapjack.Compiler.Backend.WordAlloc
