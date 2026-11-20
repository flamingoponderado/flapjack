module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Build

@[expose] public section

/-! Timestamp and fresh-reference facts used by the constant-builder proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

/-- Executing a single part preserves an enabled timestamp. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "do_part_SOME_IMP_SOME"]
theorem doPartSome {α : Type} (values : Nat → Value) (part : ClosLang.ConstPart)
    (refs resultRefs : Spt (BvlSem.Ref α)) (timestamp : Nat) (value : Value) (resultTimestamp : Option Nat)
    (run : doPart values part refs (some timestamp) = (value, resultRefs, resultTimestamp)) :
    ∃ result, resultTimestamp = some result := by
  cases part with
  | int i => simp [doPart] at run; exact ⟨timestamp, run.2.2.symm⟩
  | w64 w => simp [doPart] at run; exact ⟨timestamp, run.2.2.symm⟩
  | str text => simp [doPart] at run; exact ⟨timestamp, run.2.2.symm⟩
  | con tag indices =>
    cases indices with
    | nil => simp [doPart] at run; exact ⟨timestamp, run.2.2.symm⟩
    | cons i rest => simp [doPart] at run; exact ⟨timestamp + 1, run.2.2.symm⟩

/-- The least natural outside a sparse tree is outside its domain. The
`leastUnusedRef` implementation uses `Nat.find` and its minimality theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "least_notin_domain"]
theorem leastNotInDomain {α : Type} (refs : Spt α) :
    ¬ sptDomain refs (DataSem.leastUnusedRef refs) := by
  simp [sptDomain, DataSem.leastUnusedRef_unused]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
