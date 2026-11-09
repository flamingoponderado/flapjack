module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv

@[expose] public section

/-! Location offsets in the value invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataSem Memory

/-- Any location produced by the address projection has zero offset. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "v_inv_Loc"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_loc {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (value : Flapjack.Compiler.Backend.DataSem.Value) (state : State C F)
    (address : HeapAddress (WordLocW width)) (f : HolFiniteMapExact Nat Nat)
    (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) (label offset : Nat) :
    valueInv conf value state.refs (address, f, tf, heap) ∧
      wordAddr conf address = .loc label offset → offset = 0 := by
  rintro ⟨_, h⟩
  cases address with
  | pointer index word => simp [wordAddr] at h
  | data word =>
      cases word with
      | word word => simp [wordAddr] at h
      | loc n off =>
          simp [wordAddr] at h
          exact h.2.symm

end Flapjack.Compiler.Backend.DataToWord.Proofs
