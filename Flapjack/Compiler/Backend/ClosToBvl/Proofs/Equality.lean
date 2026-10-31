import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockCompare

/-! Reference and constructor equality in the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendCommon

/-- Shifted source blocks cannot be mistaken for closure blocks. -/
theorem shiftedTag_notClosure (tag : Nat) (fields : List BvlSem.Value) :
    ¬ BvlSem.isClosure (closTagShift tag) fields := by
  simp only [BvlSem.isClosure, closTagShift]
  split <;> omega

/-- A source reference pointer is mapped to the corresponding target pointer. -/
theorem vRel_refPtr_inv {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {flag : Bool} {ptr : Nat} {target : BvlSem.Value}
    (related : vRel maxApp f refs code (.refPtr flag ptr) target) :
    ∃ targetPtr, target = .refPtr flag targetPtr ∧ f.lookup ptr = some targetPtr := by
  cases related with
  | refPtr found => exact ⟨_, rfl, found⟩
  | closure _ closure => cases closure
  | partialClosure _ _ _ _ _ added _ closure => cases closure <;> simp [addArgs] at added

/-- Injection makes source reference equality agree with relocated equality. -/
theorem relocated_pointer_eq {f : HolFiniteMapExact Nat Nat}
    (injective : ∀ x₁ x₂ y, f.lookup x₁ = some y → f.lookup x₂ = some y → x₁ = x₂)
    {a b x y : Nat} (first : f.lookup a = some x) (second : f.lookup b = some y) :
    a = b ↔ x = y := by
  constructor
  · intro eq
    subst b
    exact Option.some.inj (first.symm.trans second)
  · intro eq
    subst y
    exact injective a b x first second

/-- Equality of related mutable-reference pointers agrees when the target
state satisfies the existing injection and frozen-byte-array exclusions. -/
theorem doEq_related_refPtrs {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (flagA flagB : Bool) (a b : Nat) (x y : BvlSem.Value)
    (first : vRel s.maxApp f t.refs t.code (.refPtr flagA a) x)
    (second : vRel s.maxApp f t.refs t.code (.refPtr flagB b) y) :
    ClosSem.doEq (.refPtr flagA a) (.refPtr flagB b) = BvlSem.doEq t.refs x y := by
  obtain ⟨targetA, rfl, mapA⟩ := vRel_refPtr_inv first
  obtain ⟨targetB, rfl, mapB⟩ := vRel_refPtr_inv second
  have pointerEq := relocated_pointer_eq states.2.2.2.1 mapA mapB
  have notFrozenA : ∀ bytes, t.refs.lookup targetA ≠ some (.byteArray true bytes) :=
    fun bytes => states.2.2.2.2.1 a targetA bytes mapA
  have notFrozenB : ∀ bytes, t.refs.lookup targetB ≠ some (.byteArray true bytes) :=
    fun bytes => states.2.2.2.2.1 b targetB bytes mapB
  cases flagA <;> cases flagB <;> simp [ClosSem.doEq, BvlSem.doEq]
  cases firstRef : t.refs.lookup targetA <;> cases secondRef : t.refs.lookup targetB <;> simp_all

/-- Equality of related byte vectors reads the same frozen target arrays. -/
theorem doEq_related_byteVectors {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (a b : List (BitVec 8)) (x y : BvlSem.Value)
    (first : vRel maxApp f refs code (.byteVector a) x)
    (second : vRel maxApp f refs code (.byteVector b) y) :
    ClosSem.doEq (.byteVector a) (.byteVector b) = BvlSem.doEq refs x y := by
  obtain ⟨targetA, rfl, foundA⟩ := vRel_byteVector_inv first
  obtain ⟨targetB, rfl, foundB⟩ := vRel_byteVector_inv second
  simp [ClosSem.doEq, BvlSem.doEq, foundA, foundB]

/-- Equality of a source byte vector and source reference remains a type
error: a relocated reference cannot point at a frozen byte array. -/
theorem doEq_byteVector_refPtr {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (bytes : List (BitVec 8)) (flag : Bool) (ptr : Nat) (x y : BvlSem.Value)
    (first : vRel s.maxApp f t.refs t.code (.byteVector bytes) x)
    (second : vRel s.maxApp f t.refs t.code (.refPtr flag ptr) y) :
    ClosSem.doEq (.byteVector bytes) (.refPtr flag ptr) = BvlSem.doEq t.refs x y := by
  obtain ⟨bytePtr, rfl, byteLookup⟩ := vRel_byteVector_inv first
  obtain ⟨targetPtr, rfl, map⟩ := vRel_refPtr_inv second
  have notFrozen : ∀ bs, t.refs.lookup targetPtr ≠ some (.byteArray true bs) :=
    fun bs => states.2.2.2.2.1 ptr targetPtr bs map
  cases flag <;> simp [ClosSem.doEq, BvlSem.doEq, byteLookup]

/-- Equality of a source reference and source byte vector remains a type
error in the reversed argument order as well. -/
theorem doEq_refPtr_byteVector {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (flag : Bool) (ptr : Nat) (bytes : List (BitVec 8)) (x y : BvlSem.Value)
    (first : vRel s.maxApp f t.refs t.code (.refPtr flag ptr) x)
    (second : vRel s.maxApp f t.refs t.code (.byteVector bytes) y) :
    ClosSem.doEq (.refPtr flag ptr) (.byteVector bytes) = BvlSem.doEq t.refs x y := by
  obtain ⟨targetPtr, rfl, map⟩ := vRel_refPtr_inv first
  obtain ⟨bytePtr, rfl, byteLookup⟩ := vRel_byteVector_inv second
  have notFrozen : ∀ bs, t.refs.lookup targetPtr ≠ some (.byteArray true bs) :=
    fun bs => states.2.2.2.2.1 ptr targetPtr bs map
  cases flag <;> simp [ClosSem.doEq, BvlSem.doEq, byteLookup]

/-- Pointwise equality correspondence lifts to the recursive list comparator. -/
theorem doEqList_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (pointwise : ∀ a b x y, vRel maxApp f refs code a x → vRel maxApp f refs code b y →
      ClosSem.doEq a b = BvlSem.doEq refs x y)
    {xs ys : List ClosSem.Value} {xs' ys' : List BvlSem.Value}
    (first : List.Forall₂ (vRel maxApp f refs code) xs xs')
    (second : List.Forall₂ (vRel maxApp f refs code) ys ys') :
    ClosSem.doEqList xs ys = BvlSem.doEqList refs xs' ys' := by
  induction first generalizing ys ys' with
  | nil => cases second <;> simp [ClosSem.doEqList, BvlSem.doEqList]
  | cons head tail ih =>
    cases second with
    | nil => simp [ClosSem.doEqList, BvlSem.doEqList]
    | cons head' tail' =>
      simp only [ClosSem.doEqList, BvlSem.doEqList, ← pointwise _ _ _ _ head head']
      cases ClosSem.doEq _ _ with
      | typeError => rfl
      | val result =>
        cases result with
        | false => rfl
        | true => exact ih tail'

/-- Equality of related ordinary blocks reduces to equality of their field
lists; shifted tags never enter the reserved closure range. -/
theorem doEq_related_blocks {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (tagA tagB : Nat) (xs ys : List ClosSem.Value) (xs' ys' : List BvlSem.Value)
    (first : List.Forall₂ (vRel maxApp f refs code) xs xs')
    (second : List.Forall₂ (vRel maxApp f refs code) ys ys')
    (fieldsEq : ClosSem.doEqList xs ys = BvlSem.doEqList refs xs' ys') :
    ClosSem.doEq (.block tagA xs) (.block tagB ys) =
      BvlSem.doEq refs (.block (closTagShift tagA) xs') (.block (closTagShift tagB) ys') := by
  simp [ClosSem.doEq, BvlSem.doEq, shiftedTag_notClosure, closTagShift_injective.eq_iff,
    first.length_eq, second.length_eq, fieldsEq]

end Flapjack.Compiler.Backend.ClosToBvl
