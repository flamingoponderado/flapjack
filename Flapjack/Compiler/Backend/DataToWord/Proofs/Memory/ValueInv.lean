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
premise. The rules have been compared with the typed source, but the finite-map
qualifier for maps nested in the source tuple is not yet supported, so no HOL
tag is claimed on this declaration. -/
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

/-- Clock monotonicity for the preliminary clocked value relation. This has
no HOL tag while the relation and its nested finite-map carriers remain
unreviewed; the original `v_inv_ck_mono` statement is captured by the probe. -/
theorem clockValueInv_mono {width : Nat} [NeZero width] :
    ∀ ck conf value refs context, ClockValueInv (width := width) ck conf value refs context →
      ∀ ck', ck' ≤ ck → ClockValueInv ck' conf value refs context := by
  intro ck
  induction ck with
  | zero =>
      intro conf value refs context related ck' bound
      have : ck' = 0 := by omega
      subst ck'
      exact related
  | succ ck ih =>
      intro conf value refs context related ck' bound
      cases related with
      | numberSmall _ _ i refs f tf heap small =>
          exact .numberSmall ck' conf i refs f tf heap small
      | numberBig _ _ i ptr refs f tf heap large found =>
          exact .numberBig ck' conf i ptr refs f tf heap large found
      | word64 _ _ w ptr refs f tf heap found =>
          exact .word64 ck' conf w ptr refs f tf heap found
      | codePtr _ _ n refs f tf heap =>
          exact .codePtr ck' conf n refs f tf heap
      | refPtr bit _ _ n refs f tf heap domain notThunk notMut =>
          exact .refPtr bit ck' conf n refs f tf heap domain notThunk notMut
      | refPtrThunk _ _ mode n value x refs f tf heap found evaluated domain cell recursive =>
          refine ClockValueInv.refPtrThunk ck' conf mode n value x refs f tf heap found evaluated domain cell ?_
          intro positive
          have r := recursive (by omega)
          have r' : ClockValueInv ck conf value refs (x, f, tf, heap) := by simpa using r
          exact ih conf value refs (x, f, tf, heap) r' (ck' - 1) (by omega)
      | refPtrThunkInlined _ _ n value x refs f tf heap found notThunk recursive =>
          refine ClockValueInv.refPtrThunkInlined ck' conf n value x refs f tf heap found notThunk ?_
          intro positive
          have r := recursive (by omega)
          have r' : ClockValueInv ck conf value refs (x, f, tf, heap) := by simpa using r
          exact ih conf value refs (x, f, tf, heap) r' (ck' - 1) (by omega)
      | blockNil _ _ stamp tag values refs f tf heap empty tagBound zeroStamp =>
          exact .blockNil ck' conf stamp tag values refs f tf heap empty tagBound zeroStamp
      | blockCons _ _ stamp tag ptr values xs refs f tf heap nonempty recursive timestamp cell =>
          refine ClockValueInv.blockCons ck' conf stamp tag ptr values xs refs f tf heap nonempty ?_ timestamp cell
          intro positive
          have r := recursive (by omega)
          have r' : ClockValueListInv ck conf refs f tf heap values xs := by simpa using r
          apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
          apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp r')
          intro value x head
          exact ih conf value refs (x, f, tf, heap) head (ck' - 1) (by omega)


/-- The unbounded value relation is the intersection of the clocked ones.
This remains untagged until the clocked relation and tuple-map representation
have been reviewed against the original. -/
def valueInv {width : Nat} [NeZero width] (conf : Config) (value : Value)
    (refs : Spt (BvlSem.Ref Value)) (context : ValueContext width) : Prop :=
  ∀ ck, ClockValueInv ck conf value refs context

/-- Unbounded relatedness can be established at arbitrarily large clocks;
monotonicity then supplies every smaller clock. This is Flapjack proof
infrastructure and does not claim a separate HOL declaration. -/
theorem valueInv_iff_unboundedClocks {width : Nat} [NeZero width] (conf : Config) (value : Value)
    (refs : Spt (BvlSem.Ref Value)) (context : ValueContext width) :
    valueInv conf value refs context ↔
      ∀ ck, ∃ larger, ck ≤ larger ∧ ClockValueInv larger conf value refs context := by
  constructor
  · intro all ck
    exact ⟨ck, Nat.le_refl _, all ck⟩
  · intro unbounded ck
    obtain ⟨larger, bound, related⟩ := unbounded ck
    exact clockValueInv_mono larger conf value refs context related ck bound

/-- Number case, over the preliminary value invariant. This remains untagged until the
underlying relation and finite-map representation are source-reviewed. -/
theorem valueInv_number {width : Nat} [NeZero width] (conf : Config) (i : Int) (refs : Spt (BvlSem.Ref Value))
    (x : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf (.number i) refs (x,f,tf,heap) ↔
      if smallInt width i then x = .data (.word (smallnum i)) else
        ∃ ptr, x = .pointer ptr (.word 0) ∧ heapLookup ptr heap = some (bignumRep i) := by
  by_cases hs : smallInt width i
  · simp only [hs, ↓reduceIte]
    constructor
    · intro h
      have related := h 0
      cases related with
      | numberSmall _ _ _ _ _ _ _ small => rfl
      | numberBig _ _ _ _ _ _ _ _ large _ => exact False.elim (large hs)
    · intro h ck
      subst x
      exact .numberSmall ck conf i refs f tf heap hs
  · simp only [hs, ↓reduceIte]
    constructor
    · intro h
      have related := h 0
      cases related with
      | numberSmall _ _ _ _ _ _ _ small => exact False.elim (hs small)
      | numberBig _ _ _ ptr _ _ _ _ _ found => exact ⟨ptr, rfl, found⟩
    · rintro ⟨ptr, rfl, found⟩ ck
      exact .numberBig ck conf i ptr refs f tf heap hs found

/-- Word64 case, over the preliminary value invariant. This remains untagged until the
underlying relation and finite-map representation are source-reviewed. -/
theorem valueInv_word64 {width : Nat} [NeZero width] (conf : Config) (word : BitVec 64) (refs : Spt (BvlSem.Ref Value))
    (x : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf (.word64 word) refs (x,f,tf,heap) ↔
      ∃ ptr, x = .pointer ptr (.word 0) ∧ heapLookup ptr heap = some (word64Rep word) := by
  constructor
  · intro h
    have related := h 0
    cases related with
    | word64 _ _ _ ptr _ _ _ _ found => exact ⟨ptr, rfl, found⟩
  · rintro ⟨ptr, rfl, found⟩ ck
    exact .word64 ck conf word ptr refs f tf heap found

/-- Code-pointer case, over the preliminary value invariant. This remains untagged until the
underlying relation and finite-map representation are source-reviewed. -/
theorem valueInv_codePtr {width : Nat} [NeZero width] (conf : Config) (n : Nat) (refs : Spt (BvlSem.Ref Value))
    (x : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf (.codePtr n) refs (x,f,tf,heap) ↔ x = .data (.loc n 0) := by
  constructor
  · intro h
    have related := h 0
    cases related with
    | codePtr => rfl
  · intro h ck
    subst x
    exact .codePtr ck conf n refs f tf heap

/-- Empty-block case, over the preliminary value invariant. This remains untagged until the
underlying relation and finite-map representation are source-reviewed. -/
theorem valueInv_emptyBlock {width : Nat} [NeZero width] (conf : Config) (stamp tag : Nat) (refs : Spt (BvlSem.Ref Value))
    (x : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf (.block stamp tag []) refs (x,f,tf,heap) ↔
      x = .data (.word (blockNil tag)) ∧ tag < 2 ^ width / 16 ∧ stamp = 0 := by
  constructor
  · intro h
    have related := h 0
    cases related with
    | blockNil _ _ _ _ _ _ _ _ _ _ bound zero => exact ⟨rfl, bound, zero⟩
    | blockCons _ _ _ _ _ _ _ _ _ _ _ nonempty _ _ _ => exact False.elim (nonempty rfl)
  · rintro ⟨rfl, bound, zero⟩ ck
    exact .blockNil ck conf stamp tag [] refs f tf heap rfl bound zero

/-- Flapjack list infrastructure: pairwise relatedness commutes with universal clock quantification. -/
theorem forallPairwise {α β : Type} (R : Nat → α → β → Prop) (xs : List α) (ys : List β) :
    (∀ ck, List.Forall₂ (R ck) xs ys) ↔ List.Forall₂ (fun x y => ∀ ck, R ck x y) xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp
      | cons y ys => constructor <;> intro h <;> first | (have bad := h 0; cases bad) | cases h
  | cons x xs ih =>
      cases ys with
      | nil => constructor <;> intro h <;> first | (have bad := h 0; cases bad) | cases h
      | cons y ys =>
          constructor
          · intro h
            apply List.Forall₂.cons
            · intro ck
              have pair := h ck
              cases pair with | cons head tail => exact head
            · apply (ih ys).mp
              intro ck
              have pair := h ck
              cases pair with | cons head tail => exact tail
          · intro h ck
            cases h with
            | cons head tail => exact .cons (head ck) ((ih ys).mpr tail ck)


/-- Inversion of the preliminary clocked relation for a nonempty block. This
remains untagged until the underlying relation and map carriers are reviewed. -/
theorem clockBlockInv {width : Nat} [NeZero width] (ck : Nat) (conf : Config) (stamp tag : Nat)
    (values : List Value) (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) (nonempty : values ≠ [])
    (related : ClockValueInv ck conf (.block stamp tag values) refs (x, f, tf, heap)) :
      ∃ ptr xs, x = .pointer ptr (.word (ptrBits conf tag xs.length)) ∧
        (ck ≠ 0 → ClockValueListInv (ck - 1) conf refs f tf heap values xs) ∧
        tf.lookup stamp = some ptr ∧ heapLookup ptr heap = some (blockRep tag xs) := by
  cases related with
  | blockNil _ _ _ _ _ _ _ _ _ empty _ _ => exact False.elim (nonempty empty)
  | blockCons _ _ _ _ ptr _ xs _ _ _ _ _ recursive timestamp cell =>
      exact ⟨ptr, xs, rfl, recursive, timestamp, cell⟩

/-- Nonempty-block case of the preliminary unbounded relation. The heap lookup
fixes the same field addresses at every clock. This remains untagged until the
underlying relation and map carriers are reviewed. -/
theorem valueInv_nonemptyBlock {width : Nat} [NeZero width] (conf : Config) (stamp tag : Nat)
    (values : List Value) (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) (nonempty : values ≠ []) :
    valueInv conf (.block stamp tag values) refs (x, f, tf, heap) ↔
      ∃ ptr xs, List.Forall₂ (fun value addr => valueInv conf value refs (addr, f, tf, heap)) values xs ∧
        tf.lookup stamp = some ptr ∧ x = .pointer ptr (.word (ptrBits conf tag xs.length)) ∧
        heapLookup ptr heap = some (blockRep tag xs) := by
  constructor
  · intro all
    obtain ⟨ptr, xs, xpos, _, timestamp, cell⟩ := clockBlockInv 0 conf stamp tag values refs x f tf heap nonempty (all 0)
    refine ⟨ptr, xs, ?_, timestamp, xpos, cell⟩
    apply (forallPairwise _ values xs).mp
    intro ck
    obtain ⟨ptr2, xs2, _, recursive, timestamp2, cell2⟩ :=
      clockBlockInv (ck + 1) conf stamp tag values refs x f tf heap nonempty (all (ck + 1))
    have hp : ptr2 = ptr := Option.some.inj (timestamp2.symm.trans timestamp)
    subst ptr2
    have hx : xs2 = xs := by
      have he := Option.some.inj (cell2.symm.trans cell)
      cases he
      rfl
    subst xs2
    have pair := recursive (by omega)
    have pair' : ClockValueListInv ck conf refs f tf heap values xs := by simpa using pair
    exact (clockValueListInv_iff _ _ _ _ _ _ _ _).mp pair'
  · rintro ⟨ptr, xs, pair, timestamp, rfl, cell⟩ ck
    refine .blockCons ck conf stamp tag ptr values xs refs f tf heap nonempty ?_ timestamp cell
    intro _
    apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
    exact pair.imp (fun value addr related => related (ck - 1))

/-- Complete block case of the preliminary unbounded relation. This remains
untagged until the underlying relation and map carriers are reviewed. -/
theorem valueInv_block {width : Nat} [NeZero width] (conf : Config) (stamp tag : Nat)
    (values : List Value) (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf (.block stamp tag values) refs (x, f, tf, heap) ↔
      if values = [] then
        x = .data (.word (blockNil tag)) ∧ tag < 2 ^ width / 16 ∧ stamp = 0
      else
        ∃ ptr xs, List.Forall₂ (fun value addr => valueInv conf value refs (addr, f, tf, heap)) values xs ∧
          tf.lookup stamp = some ptr ∧ x = .pointer ptr (.word (ptrBits conf tag xs.length)) ∧
          heapLookup ptr heap = some (blockRep tag xs) := by
  by_cases empty : values = []
  · subst values
    simpa using valueInv_emptyBlock conf stamp tag refs x f tf heap
  · simpa [empty] using valueInv_nonemptyBlock conf stamp tag values refs x f tf heap empty

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
