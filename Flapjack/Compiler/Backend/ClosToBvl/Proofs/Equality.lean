import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockCompare

/-! Reference and constructor equality in the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendCommon

/-- Shifted source blocks cannot be mistaken for closure blocks. -/
theorem shiftedTag_notClosure (tag : Nat) (fields : List BvlSem.Value) :
    ¬ BvlSem.isClosure (closTagShift tag) fields := by
  simp only [BvlSem.isClosure, closTagShift]
  split <;> omega

/-- Whether a closure-language value is a function value. -/
def sourceIsClosure : ClosSem.Value → Prop
  | .closure .. | .recclosure .. => True
  | _ => False

private theorem clRel_sourceIsClosure {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {env : List ClosSem.Value × List BvlSem.Value} {source : ClosSem.Value} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code env source target) : sourceIsClosure source := by
  cases related <;> trivial

private theorem addArgs_sourceIsClosure (source result : ClosSem.Value) (args : List ClosSem.Value)
    (isClosure : sourceIsClosure source) (added : addArgs source args = some result) :
    sourceIsClosure result := by
  cases source <;> simp_all [sourceIsClosure, addArgs]
  all_goals subst result; trivial

/-- The value relation represents exactly the source closure values as BVL
closure blocks. -/
theorem vRel_isClosure {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : ClosSem.Value} {target : BvlSem.Value}
    (related : vRel maxApp f refs code source target) :
    sourceIsClosure source ↔ (∃ tag fields, target = .block tag fields ∧ BvlSem.isClosure tag fields) := by
  cases related with
  | number => simp [sourceIsClosure]
  | word64 => simp [sourceIsClosure]
  | block fields =>
    simp only [sourceIsClosure, false_iff, not_exists]
    intro tag xs ⟨equal, isClosure⟩
    cases equal
    exact shiftedTag_notClosure _ _ isClosure
  | byteVector => simp [sourceIsClosure]
  | refPtr => simp [sourceIsClosure]
  | closure env closure =>
    have sourceClosure : sourceIsClosure source := clRel_sourceIsClosure closure
    exact ⟨fun _ => ⟨30, _, rfl, by simp [BvlSem.isClosure]⟩, fun _ => sourceClosure⟩
  | partialClosure env args nonempty bound lookup added arity closure =>
    have sourceClosure : sourceIsClosure source :=
      addArgs_sourceIsClosure _ _ _ (clRel_sourceIsClosure closure) added
    exact ⟨fun _ => ⟨31, _, rfl, by simp [BvlSem.isClosure]⟩, fun _ => sourceClosure⟩

/-- Equality distinguishes these broad value classes; references and byte
vectors share a class because byte vectors become target references. -/
def sourceEqClass : ClosSem.Value → Nat
  | .number _ => 0
  | .word64 _ => 1
  | .block .. | .closure .. | .recclosure .. => 2
  | .byteVector _ | .refPtr .. => 3

/-- Corresponding BVL equality classes. -/
def targetEqClass : BvlSem.Value → Nat
  | .number _ => 0
  | .word64 _ => 1
  | .block .. => 2
  | .refPtr .. => 3
  | .codePtr _ => 4

/-- Related values have the same broad equality class. -/
theorem vRel_eqClass {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : ClosSem.Value} {target : BvlSem.Value}
    (related : vRel maxApp f refs code source target) : sourceEqClass source = targetEqClass target := by
  cases related with
  | number | word64 | block | byteVector | refPtr => rfl
  | closure env closure =>
    have sourceClosure := clRel_sourceIsClosure closure
    cases source <;> simp_all [sourceIsClosure, sourceEqClass, targetEqClass]
  | partialClosure env args nonempty bound lookup added arity closure =>
    have sourceClosure := addArgs_sourceIsClosure _ _ _ (clRel_sourceIsClosure closure) added
    cases source <;> simp_all [sourceIsClosure, sourceEqClass, targetEqClass]

/-- Values from different source equality classes always produce a type error. -/
theorem sourceEq_class_mismatch (a b : ClosSem.Value)
    (different : sourceEqClass a ≠ sourceEqClass b) : ClosSem.doEq a b = .typeError := by
  cases a <;> cases b <;> simp_all [sourceEqClass, ClosSem.doEq]

/-- Values from different target equality classes always produce a type error. -/
theorem targetEq_class_mismatch {α : Type} (refs : HolFiniteMapExact Nat (BvlSem.Ref α))
    (a b : BvlSem.Value) (different : targetEqClass a ≠ targetEqClass b) :
    BvlSem.doEq refs a b = .typeError := by
  cases a <;> cases b <;> simp_all [targetEqClass, BvlSem.doEq]

/-- Equality agrees when the source values belong to different classes. -/
theorem doEq_class_mismatch {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (a b : ClosSem.Value) (x y : BvlSem.Value)
    (first : vRel maxApp f refs code a x) (second : vRel maxApp f refs code b y)
    (different : sourceEqClass a ≠ sourceEqClass b) :
    ClosSem.doEq a b = BvlSem.doEq refs x y := by
  have targetDifferent : targetEqClass x ≠ targetEqClass y := by
    simpa [← vRel_eqClass first, ← vRel_eqClass second] using different
  rw [sourceEq_class_mismatch a b different, targetEq_class_mismatch refs x y targetDifferent]

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

/-- Source closures and their related target closures compare equal, whether
ordinary or recursive. -/
theorem doEq_related_closures {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (a b : ClosSem.Value) (x y : BvlSem.Value)
    (first : vRel maxApp f refs code a x) (second : vRel maxApp f refs code b y)
    (closureA : sourceIsClosure a) (closureB : sourceIsClosure b) :
    ClosSem.doEq a b = BvlSem.doEq refs x y := by
  obtain ⟨tagA, fieldsA, rfl, isA⟩ := (vRel_isClosure first).mp closureA
  obtain ⟨tagB, fieldsB, rfl, isB⟩ := (vRel_isClosure second).mp closureB
  cases a <;> cases b <;> simp_all [sourceIsClosure, ClosSem.doEq, BvlSem.doEq]

/-- Comparing a closure with a non-closure is a type error in both
representations. -/
theorem doEq_closure_nonClosure {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (a b : ClosSem.Value) (x y : BvlSem.Value)
    (first : vRel maxApp f refs code a x) (second : vRel maxApp f refs code b y)
    (closureA : sourceIsClosure a) (notClosureB : ¬sourceIsClosure b) :
    ClosSem.doEq a b = BvlSem.doEq refs x y := by
  obtain ⟨tagA, fieldsA, rfl, isA⟩ := (vRel_isClosure first).mp closureA
  have notTarget : ¬ ∃ tag fields, y = .block tag fields ∧ BvlSem.isClosure tag fields :=
    fun h => notClosureB ((vRel_isClosure second).mpr h)
  cases y with
  | block tag fields =>
    have notB : ¬BvlSem.isClosure tag fields := by
      intro isB
      exact notTarget ⟨tag, fields, rfl, isB⟩
    cases a <;> cases b <;> simp_all [sourceIsClosure, ClosSem.doEq, BvlSem.doEq]
  | number | word64 | codePtr | refPtr =>
    cases a <;> cases b <;> simp_all [sourceIsClosure, ClosSem.doEq, BvlSem.doEq]

/-- Comparing a non-closure with a closure is also a type error. -/
theorem doEq_nonClosure_closure {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (a b : ClosSem.Value) (x y : BvlSem.Value)
    (first : vRel maxApp f refs code a x) (second : vRel maxApp f refs code b y)
    (notClosureA : ¬sourceIsClosure a) (closureB : sourceIsClosure b) :
    ClosSem.doEq a b = BvlSem.doEq refs x y := by
  obtain ⟨tagB, fieldsB, rfl, isB⟩ := (vRel_isClosure second).mp closureB
  have notTarget : ¬ ∃ tag fields, x = .block tag fields ∧ BvlSem.isClosure tag fields :=
    fun h => notClosureA ((vRel_isClosure first).mpr h)
  cases x with
  | block tag fields =>
    have notA : ¬BvlSem.isClosure tag fields := by
      intro isA
      exact notTarget ⟨tag, fields, rfl, isA⟩
    cases a <;> cases b <;> simp_all [sourceIsClosure, ClosSem.doEq, BvlSem.doEq]
  | number | word64 | codePtr | refPtr =>
    cases a <;> cases b <;> simp_all [sourceIsClosure, ClosSem.doEq, BvlSem.doEq]

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
