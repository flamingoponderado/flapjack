import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.Compiler.Backend.WordAlloc

@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "is_alloc_var_add"]
theorem isAllocVarAdd (next : Nat) (h : isAllocVar next) :
    isAllocVar (next + 4) := by
  simpa [isAllocVar, Nat.add_mod] using h

@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "is_stack_var_add"]
theorem isStackVarAdd (next : Nat) (h : isStackVar next) :
    isStackVar (next + 4) := by
  simpa [isStackVar, Nat.add_mod] using h

end Flapjack.Compiler.Backend.WordAlloc
