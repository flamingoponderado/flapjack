module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.MutCons
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CellUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayStore

@[expose] public section

/-!
# Writing the hole of an unfinalised mutable block

Counterparts of `v_inv_BlockRep_upd_lemma` and `update_mutblock_thm` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`t IN FDOM tf` is `mapDomain tf t`, `tf ' t` is `holFapply tf t`,
`LUPDATE x n l` is `l.set n x` and `v_inv_ck` is `ClockValueInv`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- The clocked value invariant survives a heap change at a block cell `p`
that no timestamp targets, when every other cell is kept. Flapjack proof
infrastructure for `v_inv_BlockRep_upd_lemma`. -/
theorem clockValueInv_blockRepUpd {width : Nat} [NeZero width] (ck : Nat)
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (f tf : HolFiniteMapExact Nat Nat) (heap heap2 : ValueHeap width) (p tag : Nat)
    (zs : List (HeapAddress (WordLocW width)))
    (cellP : heapLookup p heap = some (blockRep tag zs))
    (noStamp : ∀ t, mapDomain tf t → holFapply tf t ≠ p)
    (kept : ∀ m y, m ≠ p ∧ heapLookup m heap = some y → heapLookup m heap2 = some y) :
    ∀ (value : Flapjack.Compiler.Backend.DataSem.Value) (address : HeapAddress (WordLocW width)),
      ClockValueInv ck conf value refs (address, f, tf, heap) →
      ClockValueInv ck conf value refs (address, f, tf, heap2) := by
  have keep : ∀ m y, heapLookup m heap = some y → y ≠ blockRep tag zs → heapLookup m heap2 = some y := by
    intro m y found ne
    apply kept m y ⟨?_, found⟩
    rintro rfl
    rw [cellP] at found
    exact ne (Option.some.inj found).symm
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value address related
    cases related with
    | numberSmall _ _ i _ _ _ _ small => exact .numberSmall ck conf i refs f tf heap2 small
    | numberBig _ _ i ptr _ _ _ _ large found =>
      apply ClockValueInv.numberBig ck conf i ptr refs f tf heap2 large
      apply keep ptr _ found
      simp [bignumRep, blockRep]
    | word64 _ _ word ptr _ _ _ _ found =>
      apply ClockValueInv.word64 ck conf word ptr refs f tf heap2
      apply keep ptr _ found
      unfold word64Rep
      split <;> simp [blockRep]
    | codePtr _ _ n _ _ _ _ => exact .codePtr ck conf n refs f tf heap2
    | refPtr bit _ _ n _ _ _ _ domain notThunk notMut =>
      exact .refPtr bit ck conf n refs f tf heap2 domain notThunk notMut
    | refPtrThunk _ _ mode n body x _ _ _ _ found evaluated domain cell recursive =>
      refine .refPtrThunk ck conf mode n body x refs f tf heap2 found evaluated domain ?_ ?_
      · apply keep _ _ cell
        simp [thunkBlock, blockRep]
      · intro positive
        exact ih (ck - 1) (by omega) body x (recursive positive)
    | refPtrThunkInlined _ _ n body x _ _ _ _ found notThunk recursive =>
      refine .refPtrThunkInlined ck conf n body address refs f tf heap2 found notThunk ?_
      intro positive
      exact ih (ck - 1) (by omega) body address (recursive positive)
    | blockNil _ _ stamp tag' values _ _ _ _ empty bound zero =>
      exact .blockNil ck conf stamp tag' values refs f tf heap2 empty bound zero
    | blockCons _ _ stamp tag' ptr values xs _ _ _ _ nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag' ptr values xs refs f tf heap2 nonempty ?_ timestamp ?_
      · intro positive
        apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
        apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
        intro child addr childInv
        exact ih (ck - 1) (by omega) child addr childInv
      · apply kept ptr _ ⟨?_, cell⟩
        have := noStamp stamp ⟨ptr, timestamp⟩
        rwa [holFapply_of_lookup timestamp] at this

/-- HOL `v_inv_BlockRep_upd_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_BlockRep_upd_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_blockRepUpd_lemma {width : Nat} [NeZero width] :
    ∀ (ck : Nat) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (p tag : Nat)
      (zs : List (HeapAddress (WordLocW width))),
      valueInv conf v1 refs (x, f, tf, heap) ∧ heapLookup p heap = some (blockRep tag zs) ∧
          (∀ t, mapDomain tf t → holFapply tf t ≠ p) ∧
          (∀ m y, m ≠ p ∧ heapLookup m heap = some y → heapLookup m heap2 = some y) →
        ClockValueInv ck conf v1 refs (x, f, tf, heap2) := by
  rintro ck conf v1 refs x f tf heap heap2 p tag zs ⟨inv, cellP, noStamp, kept⟩
  exact clockValueInv_blockRepUpd ck conf refs f tf heap heap2 p tag zs cellP noStamp kept v1 x (inv ck)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
