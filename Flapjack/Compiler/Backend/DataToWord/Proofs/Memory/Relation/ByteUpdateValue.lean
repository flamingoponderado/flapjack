module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateRefs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv

@[expose] public section

/-! Value-observation preservation when inserting a byte-array reference. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Inserting a byte array cannot turn a value that is not a thunk into a
thunk. An invalid reference at the insertion key becomes non-thunk as well. -/
theorem destThunk_notThunk_insertByteArray (value : Value) (refs : Spt (BvlSem.Ref Value))
    (ptr : Nat) (flag : Bool) (bytes : List (BitVec 8))
    (notThunk : destThunk value refs = .notThunk) :
    destThunk value (sptInsert ptr (.byteArray flag bytes) refs) = .notThunk := by
  cases value with
  | refPtr bit index =>
    by_cases same : index = ptr
    · subst index
      simp [destThunk, sptLookup_sptInsert_same]
    · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs same] using notThunk
  | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]

/-- Inserting a byte array leaves the pointer annotation unchanged when the
previous cell was absent or another byte array. -/
theorem refPtrAnnot_insertByteArray {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr index : Nat) (flag : Bool) (bytes : List (BitVec 8))
    (safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    refPtrAnnot (width := width) conf (sptLookup index (sptInsert ptr (.byteArray flag bytes) refs)) =
      refPtrAnnot conf (sptLookup index refs) := by
  by_cases same : index = ptr
  · subst index
    rcases safe with absent | ⟨oldFlag, oldBytes, present⟩
    · simp [sptLookup_sptInsert_same, absent, refPtrAnnot]
    · simp [sptLookup_sptInsert_same, present, refPtrAnnot]
  · rw [sptLookup_sptInsert_ne ptr index _ refs same]

/-- An existing thunk survives insertion at a different key; the overwritten
cell cannot be a thunk under the byte-array side condition. -/
theorem lookupThunk_insertByteArray (refs : Spt (BvlSem.Ref Value)) (ptr index : Nat)
    (flag : Bool) (bytes : List (BitVec 8)) (mode : AstHOL.ThunkMode) (body : Value)
    (safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes))
    (found : sptLookup index refs = some (.thunk mode body)) :
    sptLookup index (sptInsert ptr (.byteArray flag bytes) refs) = some (.thunk mode body) := by
  by_cases same : index = ptr
  · subst index
    rcases safe with absent | ⟨oldFlag, oldBytes, present⟩ <;> simp_all
  · simpa [sptLookup_sptInsert_ne ptr index _ refs same] using found

/-- The clocked value relation survives inserting a byte-array reference.
This is a proof-side step toward the source theorem, retaining its crucial
condition that an existing cell at the insertion key is already a byte array. -/
theorem clockValueInv_insertByteArray {width : Nat} [NeZero width] (ck : Nat)
    (conf : Config) (refs : Spt (BvlSem.Ref Value)) (ptr : Nat) (flag : Bool) (bytes : List (BitVec 8))
    (safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    ∀ (value : Value) (context : ValueContext width), ClockValueInv ck conf value refs context →
      ClockValueInv ck conf value (sptInsert ptr (.byteArray flag bytes) refs) context := by
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value context related
    cases related with
    | numberSmall _ _ i _ f tf heap small => exact .numberSmall ck conf i _ f tf heap small
    | numberBig _ _ i address _ f tf heap large found => exact .numberBig ck conf i address _ f tf heap large found
    | word64 _ _ word address _ f tf heap found => exact .word64 ck conf word address _ f tf heap found
    | codePtr _ _ n _ f tf heap => exact .codePtr ck conf n _ f tf heap
    | refPtr bit _ _ n _ f tf heap domain notThunk notMut =>
      have ann := refPtrAnnot_insertByteArray (width := width) conf refs ptr n flag bytes safe
      rw [← ann]
      apply ClockValueInv.refPtr bit ck conf n _ f tf heap domain
      · intro mode body
        by_cases same : n = ptr
        · subst n; simp [sptLookup_sptInsert_same]
        · simpa [sptLookup_sptInsert_ne ptr n _ refs same] using notThunk mode body
      · intro tag finalised left body right lookup
        by_cases same : n = ptr
        · subst n; simp [sptLookup_sptInsert_same] at lookup
        · exact notMut tag finalised left body right (by simpa [sptLookup_sptInsert_ne ptr n _ refs same] using lookup)
    | refPtrThunk _ _ mode n body x _ f tf heap found evaluated domain cell recursive =>
      refine .refPtrThunk ck conf mode n body x _ f tf heap
        (lookupThunk_insertByteArray refs ptr n flag bytes mode body safe found)
        (fun h => destThunk_notThunk_insertByteArray body refs ptr flag bytes (evaluated h)) domain cell ?_
      intro positive
      exact ih (ck - 1) (by omega) body _ (recursive positive)
    | refPtrThunkInlined _ _ n body x _ f tf heap found notThunk recursive =>
      refine .refPtrThunkInlined ck conf n body x _ f tf heap
        (lookupThunk_insertByteArray refs ptr n flag bytes .evaluated body safe found)
        (destThunk_notThunk_insertByteArray body refs ptr flag bytes notThunk) ?_
      intro positive
      exact ih (ck - 1) (by omega) body _ (recursive positive)
    | blockNil _ _ stamp tag values _ f tf heap empty bound zero =>
      exact .blockNil ck conf stamp tag values _ f tf heap empty bound zero
    | blockCons _ _ stamp tag address values xs _ f tf heap nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag address values xs _ f tf heap nonempty ?_ timestamp cell
      intro positive
      apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
      apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
      intro child x childInv
      exact ih (ck - 1) (by omega) child _ childInv

/-- A value invariant remains true when a byte-array cell is inserted, as long
as an existing cell at that key is itself a byte array. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_ByteArray_insert"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_insertByteArray {width : Nat} [NeZero width] (conf : Config)
    (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (address : HeapAddress (WordLocW width))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) (ptr : Nat) (flag : Bool)
    (bytes : List (BitVec 8))
    (valid : valueInv conf value refs (address, f, tf, heap) ∧
      (sptMem ptr refs → ∃ oldFlag oldBytes,
        sptLookup ptr refs = some (.byteArray oldFlag oldBytes))) :
    valueInv conf value (sptInsert ptr (.byteArray flag bytes) refs) (address, f, tf, heap) := by
  have safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes) := by
    by_cases absent : sptLookup ptr refs = none
    · exact Or.inl absent
    · apply Or.inr
      apply valid.2
      cases found : sptLookup ptr refs with
      | none => exact False.elim (absent found)
      | some cell => simp [sptMem, sptDomain, found]
  intro ck
  exact clockValueInv_insertByteArray ck conf refs ptr flag bytes safe value _ (valid.1 ck)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
