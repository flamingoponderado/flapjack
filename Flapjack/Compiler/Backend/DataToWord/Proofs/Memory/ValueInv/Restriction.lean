import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Reference
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Stack

/-! Timestamp-map restriction for the data-to-word value invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Restrict a finite map to a predicate. This Flapjack helper uses the
canonical finite-support carrier and has the lookup behavior of HOL DRESTRICT. -/
noncomputable def restrictTimestampMap (map : HolFiniteMapExact Nat Nat) (keep : Nat → Prop) :
    HolFiniteMapExact Nat Nat := by
  classical
  refine ⟨fun key => if keep key then map.lookup key else none, ?_⟩
  obtain ⟨keys, finite⟩ := map.finiteSupport
  refine ⟨keys, ?_⟩
  intro key present
  apply finite key
  by_cases h : keep key <;> simp [h] at present
  exact present

/-- Restricting a map preserves the lookup of a kept key. -/
theorem restrictTimestampMap_lookup (map : HolFiniteMapExact Nat Nat) (keep : Nat → Prop)
    (key : Nat) (kept : keep key) : (restrictTimestampMap map keep).lookup key = map.lookup key := by
  classical
  simp [restrictTimestampMap, kept]

/-- A restricted lookup returns a value exactly when the key is selected and
the original lookup returns it. -/
theorem restrictTimestampMap_lookup_some (map : HolFiniteMapExact Nat Nat) (keep : Nat → Prop)
    (key value : Nat) : (restrictTimestampMap map keep).lookup key = some value ↔
      keep key ∧ map.lookup key = some value := by
  classical
  by_cases selected : keep key <;> simp [restrictTimestampMap, selected]

/-- Map a pairwise list relation while allowing each step to use membership
in the original left list. This is Flapjack list infrastructure. -/
theorem forall2_imp_member {α β : Type} {R S : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys)
    (step : ∀ x y, x ∈ xs → R x y → S x y) : List.Forall₂ S xs ys := by
  induction related with
  | nil => exact .nil
  | @cons x y xs ys head tail ih =>
      refine .cons (step x y (by simp) head) ?_
      exact ih (fun a b member hab => step a b (by simp [member]) hab)

/-- A timestamp in a direct block child occurs in the enclosing block.
This is Flapjack proof infrastructure. -/
theorem blockChildTimestamp (stamp tag : Nat) (values : List Value) (child : Value) (ts : Nat)
    (member : child ∈ values) (timestamp : ts ∈ valueTimestamps child) :
    ts ∈ valueTimestamps (.block stamp tag values) := by
  simp only [valueTimestamps, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨child, member, timestamp⟩

/-- A timestamp in a stored thunk value occurs in the source reference set.
This is Flapjack proof infrastructure. -/
theorem thunkTimestampInAll (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (n : Nat) (mode : AstHOL.ThunkMode) (value : Value)
    (found : sptLookup n refs = some (.thunk mode value)) (ts : Nat)
    (timestamp : ts ∈ valueTimestamps value) : allTimestamps refs stack ts := by
  refine ⟨value, Or.inl ⟨n, .thunk mode value, found, ?_⟩, timestamp⟩
  simp [findRef]

/-- Clocked consequence of restricting the timestamp map. This is the
inductive core of the source restriction theorem; the source-shaped statement
over all clocks is proved separately. -/
theorem clockValueInv_restrict {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (stack : List Value) (keep : Nat → Prop) :
    ∀ ck value x, valueInv conf value refs (x, f, tf, heap) →
      (∀ ts, ts ∈ valueTimestamps value → keep ts) →
      (∀ ts, allTimestamps refs stack ts → keep ts) →
      ClockValueInv ck conf value refs (x, f, restrictTimestampMap tf keep, heap) := by
  intro ck
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value x related keptValues keptRefs
    cases value with
    | number i =>
        have source := related ck
        cases source with
        | numberSmall _ _ _ _ _ _ _ small =>
            exact .numberSmall ck conf i refs f (restrictTimestampMap tf keep) heap small
        | numberBig _ _ _ ptr _ _ _ _ large found =>
            exact .numberBig ck conf i ptr refs f (restrictTimestampMap tf keep) heap large found
    | word64 word =>
        have source := related ck
        cases source with
        | word64 _ _ _ ptr _ _ _ _ found =>
            exact .word64 ck conf word ptr refs f (restrictTimestampMap tf keep) heap found
    | codePtr n =>
        have source := related ck
        cases source with
        | codePtr => exact .codePtr ck conf n refs f (restrictTimestampMap tf keep) heap
    | refPtr bit n =>
        rcases (valueInv_refPtr conf bit n refs x f tf heap).mp related with
          ⟨domain, notThunk, notMut, rfl⟩ |
          ⟨mode, child, addr, found, safe, domain, cell, childInv, bitFalse, rfl⟩ |
          ⟨child, found, safe, bitFalse, childInv⟩
        · exact .refPtr bit ck conf n refs f (restrictTimestampMap tf keep) heap domain notThunk notMut
        · subst bit
          refine .refPtrThunk ck conf mode n child addr refs f (restrictTimestampMap tf keep) heap
            found safe domain cell ?_
          intro positive
          exact ih (ck - 1) (by omega) child addr childInv
            (fun ts member => keptRefs ts (thunkTimestampInAll refs stack n mode child found ts member)) keptRefs
        · subst bit
          refine .refPtrThunkInlined ck conf n child x refs f (restrictTimestampMap tf keep) heap
            found safe ?_
          intro positive
          exact ih (ck - 1) (by omega) child x childInv
            (fun ts member => keptRefs ts (thunkTimestampInAll refs stack n .evaluated child found ts member)) keptRefs
    | block stamp tag values =>
        have source := (valueInv_block conf stamp tag values refs x f tf heap).mp related
        by_cases empty : values = []
        · subst values
          simp only [↓reduceIte] at source
          obtain ⟨rfl, bound, zero⟩ := source
          exact .blockNil ck conf stamp tag [] refs f (restrictTimestampMap tf keep) heap rfl bound zero
        · simp only [empty, ↓reduceIte] at source
          obtain ⟨ptr, addresses, pair, timestamp, rfl, cell⟩ := source
          refine .blockCons ck conf stamp tag ptr values addresses refs f (restrictTimestampMap tf keep) heap
            empty ?_ ?_ cell
          · intro positive
            apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
            apply forall2_imp_member pair
            intro child addr member childInv
            exact ih (ck - 1) (by omega) child addr childInv
              (fun ts ht => keptValues ts (blockChildTimestamp stamp tag values child ts member ht)) keptRefs
          · rw [restrictTimestampMap_lookup tf keep stamp]
            · exact timestamp
            · exact keptValues stamp (by simp [valueTimestamps])

/-- The clocked source restriction lemma. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_tf_restrict_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem clockValueInv_tfRestrict {width : Nat} [NeZero width] (conf : Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (keep : Nat → Prop)
    (ck : Nat) (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f : HolFiniteMapExact Nat Nat)
    (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf value refs (x, f, tf, heap) →
      ((∀ ts, ts ∈ valueTimestamps value → keep ts) ∧
       (∀ ts, allTimestamps refs stack ts → keep ts)) →
      ClockValueInv ck conf value refs (x, f, restrictTimestampMap tf keep, heap) := by
  intro related conditions
  exact clockValueInv_restrict conf refs f tf heap stack keep ck value x related conditions.1 conditions.2

/-- A value invariant survives restricting the timestamp map to a set that
contains the value's timestamps and all timestamps reachable from references
and the stack. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_tf_restrict"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_tfRestrict {width : Nat} [NeZero width] (conf : Config)
    (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (x : HeapAddress (WordLocW width))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (heap : ValueHeap width) (keep : Nat → Prop) :
    valueInv conf value refs (x, f, tf, heap) ∧
      (∀ ts, ts ∈ valueTimestamps value → keep ts) ∧
      (∀ ts, allTimestamps refs stack ts → keep ts) →
    valueInv conf value refs (x, f, restrictTimestampMap tf keep, heap) := by
  rintro ⟨related, keptValues, keptRefs⟩ ck
  exact clockValueInv_restrict conf refs f tf heap stack keep ck value x related keptValues keptRefs

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
