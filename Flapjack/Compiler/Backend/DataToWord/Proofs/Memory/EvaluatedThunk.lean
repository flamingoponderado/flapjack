module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Representation
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Value
public import Flapjack.Misc.Sptree

@[expose] public section

/-!
# Thunk blocks and evaluated thunk references

Counterparts of `ThunkBlock_11`, `dest_evaluated_thunk_rel` and
`evaluated_thunk_ptr_def` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- HOL `ThunkBlock_11`: thunk blocks are injective in mode and address. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ThunkBlock_11"]
theorem thunkBlock_inj {α β : Type} (ev1 : AstHOL.ThunkMode) (x1 : HeapAddress α)
    (ev2 : AstHOL.ThunkMode) (x2 : HeapAddress α) :
    (thunkBlock ev1 x1 : HeapElement α (HeapTag × List β)) = thunkBlock ev2 x2 ↔
      ev1 = ev2 ∧ x1 = x2 := by
  constructor
  · intro h
    simp only [thunkBlock, HeapElement.dataElement.injEq, List.cons.injEq, Prod.mk.injEq,
      HeapTag.thunkTag.injEq] at h
    exact ⟨h.2.2.1, h.1.1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- HOL `dest_evaluated_thunk_rel`: an evaluated thunk block is related to the
address it stores. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "dest_evaluated_thunk_rel"]
inductive DestEvaluatedThunkRel {α β : Type} :
    HeapElement α (HeapTag × List β) → HeapAddress α → Prop where
  | intro (x : HeapAddress α) : DestEvaluatedThunkRel (thunkBlock .evaluated x) x

/-- The generated `dest_evaluated_thunk_rel_cases` characterisation. -/
theorem destEvaluatedThunkRel_cases {α β : Type} (a0 : HeapElement α (HeapTag × List β))
    (a1 : HeapAddress α) : DestEvaluatedThunkRel a0 a1 ↔ a0 = thunkBlock .evaluated a1 := by
  constructor
  · rintro ⟨x⟩
    rfl
  · rintro rfl
    exact .intro a1

/-- HOL `evaluated_thunk_ptr_def`: reference `n` holds an evaluated thunk. The
reference payload type is polymorphic as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "evaluated_thunk_ptr_def"]
def evaluatedThunkPtr {α : Type} (refs : Spt (BvlSem.Ref α)) (n : Nat) : Prop :=
  ∃ v, sptLookup n refs = some (.thunk .evaluated v)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
