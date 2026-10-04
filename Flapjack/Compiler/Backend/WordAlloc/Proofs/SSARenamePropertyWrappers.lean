import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameProperties
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full native move-renaming wrapper: the original producer equality precedes
the allocation-or-stack/map premise. The program retains its arbitrary positive
word dimension; all four output conclusions are unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem listNextVarRenameMoveProps {width : Nat} [NeZero width]
    (names : List Nat) (ssa : Spt Nat) (next : Nat)
    (move : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : listNextVarRenameMove ssa next names = (move, ssaOut, nextOut))
    (valid : (isAllocVar next ∨ isStackVar next) ∧ ssaMapOK next ssa) :
    next ≤ nextOut ∧ (isAllocVar next → isAllocVar nextOut) ∧
      (isStackVar next → isStackVar nextOut) ∧ ssaMapOK nextOut ssaOut := by
  generalize renamed : listNextVarRename names ssa next = result
  rcases result with ⟨renamedNames, renamedSSA, renamedNext⟩
  simp only [listNextVarRenameMove, renamed, Prod.mk.injEq] at produced
  rcases produced with ⟨_, rfl, rfl⟩
  exact listNextVarRenameProps names ssa next renamedNames renamedSSA renamedNext renamed valid

/-- Full native single-name wrapper, with arbitrary natural names/counters and
native maps. No tree validity, distinctness or new premise is introduced. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "next_var_rename_props"]
theorem nextVarRenameProps (name : Nat) (ssa : Spt Nat) (next : Nat)
    (nameOut : Nat) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : nextVarRename name ssa next = (nameOut, ssaOut, nextOut))
    (valid : (isAllocVar next ∨ isStackVar next) ∧ ssaMapOK next ssa) :
    next ≤ nextOut ∧ (isAllocVar next → isAllocVar nextOut) ∧
      (isStackVar next → isStackVar nextOut) ∧ ssaMapOK nextOut ssaOut := by
  simp only [nextVarRename, Prod.mk.injEq] at produced
  rcases produced with ⟨rfl, rfl, rfl⟩
  exact listNextVarRenameProps [name] ssa next [next] (sptInsert name next ssa)
    (next + 4) rfl valid

end Flapjack.Compiler.Backend.WordAlloc
