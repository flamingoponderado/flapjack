import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values
import Flapjack.Compiler.Backend.Semantics.DataSem.Control
import Flapjack.Misc.FiniteMapApply
import Mathlib.Data.List.Forall2

/-! Clock-indexed value relation for the data-to-word memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

abbrev ValueHeap (width : Nat) [NeZero width] :=
  List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))

abbrev ValueContext (width : Nat) [NeZero width] :=
  HeapAddress (WordLocW width) × HolFiniteMapExact Nat Nat × HolFiniteMapExact Nat Nat × ValueHeap width

mutual
/-- Clock-indexed value invariant, factored through a mutual list relation to
meet Lean's positivity rules. The HOL source has a single `v_inv_ck` relation
with an EVERY2 premise. The list helper below is proved equivalent to that
premise, but the combined finite-map qualifier for maps nested in the source
tuple and the full source correspondence still require review, so no HOL tag
is claimed on this declaration yet. -/
inductive ClockValueInv {width : Nat} [NeZero width] :
    Nat → Config → Value → Spt (BvlSem.Ref Value) → ValueContext width → Prop where
  | numberSmall (ck : Nat) (conf : Config) (i : Int) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (small : smallInt width i) :
      ClockValueInv ck conf (.number i) refs (.data (.word (smallnum i)), f, tf, heap)
  | numberBig (ck : Nat) (conf : Config) (i : Int) (ptr : Nat) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (large : ¬ smallInt width i) (found : heapLookup ptr heap = some (bignumRep i)) :
      ClockValueInv ck conf (.number i) refs (.pointer ptr (.word 0), f, tf, heap)
  | word64 (ck : Nat) (conf : Config) (w : BitVec 64) (ptr : Nat) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (found : heapLookup ptr heap = some (word64Rep w)) :
      ClockValueInv ck conf (.word64 w) refs (.pointer ptr (.word 0), f, tf, heap)
  | codePtr (ck : Nat) (conf : Config) (n : Nat) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
      ClockValueInv ck conf (.codePtr n) refs (.data (.loc n 0), f, tf, heap)
  | refPtr (bit : Bool) (ck : Nat) (conf : Config) (n : Nat) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (domain : ∃ ptr, f.lookup n = some ptr)
      (notThunk : ∀ mode value, sptLookup n refs ≠ some (.thunk mode value))
      (notPointerMutBlock : ∀ tag finalised left child right,
        sptLookup n refs = some (.mutBlock tag finalised left child right) → bit = false) :
      ClockValueInv ck conf (.refPtr bit n) refs
        (.pointer (holFapply f n) (refPtrAnnot conf (sptLookup n refs)), f, tf, heap)
  | refPtrThunk (ck : Nat) (conf : Config) (mode : AstHOL.ThunkMode) (n : Nat) (value : Value)
      (x : HeapAddress (WordLocW width)) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (found : sptLookup n refs = some (.thunk mode value))
      (evaluated : mode = .evaluated → destThunk value refs = .notThunk)
      (domain : ∃ ptr, f.lookup n = some ptr)
      (cell : heapLookup (holFapply f n) heap = some (thunkBlock mode x))
      (recursive : ck ≠ 0 → ClockValueInv (ck - 1) conf value refs (x, f, tf, heap)) :
      ClockValueInv ck conf (.refPtr false n) refs (.pointer (holFapply f n) (.word 0), f, tf, heap)
  | refPtrThunkInlined (ck : Nat) (conf : Config) (n : Nat) (value : Value)
      (x : HeapAddress (WordLocW width)) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (found : sptLookup n refs = some (.thunk .evaluated value))
      (notThunk : destThunk value refs = .notThunk)
      (recursive : ck ≠ 0 → ClockValueInv (ck - 1) conf value refs (x, f, tf, heap)) :
      ClockValueInv ck conf (.refPtr false n) refs (x, f, tf, heap)
  | blockNil (ck : Nat) (conf : Config) (stamp tag : Nat) (values : List Value)
      (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (empty : values = []) (tagBound : tag < 2 ^ width / 16) (zeroStamp : stamp = 0) :
      ClockValueInv ck conf (.block stamp tag values) refs (.data (.word (blockNil tag)), f, tf, heap)
  | blockCons (ck : Nat) (conf : Config) (stamp tag ptr : Nat) (values : List Value)
      (xs : List (HeapAddress (WordLocW width))) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (nonempty : values ≠ [])
      (recursive : ck ≠ 0 → ClockValueListInv (ck - 1) conf refs f tf heap values xs)
      (timestamp : tf.lookup stamp = some ptr) (cell : heapLookup ptr heap = some (blockRep tag xs)) :
      ClockValueInv ck conf (.block stamp tag values) refs
        (.pointer ptr (.word (ptrBits conf tag xs.length)), f, tf, heap)

/-- Positivity helper for the source's EVERY2 recursive premise. -/
inductive ClockValueListInv {width : Nat} [NeZero width] :
    Nat → Config → Spt (BvlSem.Ref Value) → HolFiniteMapExact Nat Nat → HolFiniteMapExact Nat Nat →
      ValueHeap width → List Value → List (HeapAddress (WordLocW width)) → Prop where
  | nil (ck : Nat) (conf : Config) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
      ClockValueListInv ck conf refs f tf heap [] []
  | cons (ck : Nat) (conf : Config) (refs : Spt (BvlSem.Ref Value))
      (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) (value : Value)
      (x : HeapAddress (WordLocW width)) (values : List Value) (xs : List (HeapAddress (WordLocW width)))
      (head : ClockValueInv ck conf value refs (x, f, tf, heap))
      (tail : ClockValueListInv ck conf refs f tf heap values xs) :
      ClockValueListInv ck conf refs f tf heap (value :: values) (x :: xs)
end

/-- The list helper is exactly the pairwise relation used in the HOL rule. -/
theorem clockValueListInv_iff {width : Nat} [NeZero width] (ck : Nat) (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (values : List Value) (xs : List (HeapAddress (WordLocW width))) :
    ClockValueListInv ck conf refs f tf heap values xs ↔
      List.Forall₂ (fun value x => ClockValueInv ck conf value refs (x, f, tf, heap)) values xs := by
  induction values generalizing xs with
  | nil =>
      cases xs <;> constructor <;> intro related <;> cases related <;> constructor
  | cons value values ih =>
      cases xs with
      | nil => constructor <;> intro related <;> cases related
      | cons x xs =>
          constructor
          · intro related
            cases related with
            | cons _ _ _ _ _ _ _ _ _ _ head tail =>
                exact .cons head ((ih xs).mp tail)
          · intro related
            cases related with
            | cons head tail =>
                exact .cons ck conf refs f tf heap value x values xs head ((ih xs).mpr tail)

/-- The unbounded value relation is the intersection of the clocked ones.
This remains untagged until the clocked relation and tuple-map representation
have been reviewed against the original. -/
def valueInv {width : Nat} [NeZero width] (conf : Config) (value : Value)
    (refs : Spt (BvlSem.Ref Value)) (context : ValueContext width) : Prop :=
  ∀ ck, ClockValueInv ck conf value refs context

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
