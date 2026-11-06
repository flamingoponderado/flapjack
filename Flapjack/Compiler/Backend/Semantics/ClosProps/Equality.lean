import Flapjack.Compiler.Backend.Semantics.ClosProps.ListRelations

/-! Structural equality under simple closure-value relations. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Constructor-level consequences of a simple value relation. This
Lean-side view is proof infrastructure for equality preservation. -/
inductive SimpleValueView (vr : Value → Value → Prop) : Value → Value → Prop where
  | number (n : Int) : SimpleValueView vr (.number n) (.number n)
  | word64 (w : BitVec 64) : SimpleValueView vr (.word64 w) (.word64 w)
  | byteVector (bs : List (BitVec 8)) : SimpleValueView vr (.byteVector bs) (.byteVector bs)
  | refPtr (b : Bool) (n : Nat) : SimpleValueView vr (.refPtr b n) (.refPtr b n)
  | block (tag : Nat) (xs ys : List Value) :
      List.Forall₂ vr xs ys → SimpleValueView vr (.block tag xs) (.block tag ys)
  | closureClosure (l₁ l₂ : Option Nat) (a₁ a₂ e₁ e₂ : List Value)
      (n₁ n₂ : Nat) (b₁ b₂ : ClosLang.Exp) :
      SimpleValueView vr (.closure l₁ a₁ e₁ n₁ b₁) (.closure l₂ a₂ e₂ n₂ b₂)
  | closureRec (l₁ l₂ : Option Nat) (a₁ a₂ e₁ e₂ : List Value)
      (n₁ n₂ : Nat) (b₁ : ClosLang.Exp) (fs₂ : List (Nat × ClosLang.Exp)) :
      SimpleValueView vr (.closure l₁ a₁ e₁ n₁ b₁) (.recclosure l₂ a₂ e₂ fs₂ n₂)
  | recClosure (l₁ l₂ : Option Nat) (a₁ a₂ e₁ e₂ : List Value)
      (n₁ n₂ : Nat) (fs₁ : List (Nat × ClosLang.Exp)) (b₂ : ClosLang.Exp) :
      SimpleValueView vr (.recclosure l₁ a₁ e₁ fs₁ n₁) (.closure l₂ a₂ e₂ n₂ b₂)
  | recRec (l₁ l₂ : Option Nat) (a₁ a₂ e₁ e₂ : List Value)
      (n₁ n₂ : Nat) (fs₁ fs₂ : List (Nat × ClosLang.Exp)) :
      SimpleValueView vr (.recclosure l₁ a₁ e₁ fs₁ n₁) (.recclosure l₂ a₂ e₂ fs₂ n₂)

/-- Extract the corresponding constructor view from the generic relation. -/
theorem simpleValRel_view (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (left right : Value) (related : vr left right) : SimpleValueView vr left right := by
  cases right with
  | number n =>
    have h := (simple.1 left n).mp related
    subst left; exact .number n
  | word64 w =>
    have h := (simple.2.2.1 left w).mp related
    subst left; exact .word64 w
  | byteVector bs =>
    have h := (simple.2.2.2.1 left bs).mp related
    subst left; exact .byteVector bs
  | refPtr b n =>
    have h := (simple.2.2.2.2.1 left n b).mp related
    subst left; exact .refPtr b n
  | block tag fields =>
    obtain ⟨leftFields, rfl, rel⟩ := (simple.2.1 left fields tag).mp related
    exact .block tag leftFields fields rel
  | closure loc args env arity body =>
    have h := simple.2.2.2.2.2.1 body arity env args loc left related
    cases left <;> simp_all [isClos]
    all_goals first | exact .closureClosure .. | exact .recClosure ..
  | recclosure loc args env funs index =>
    have h := simple.2.2.2.2.2.2 index funs env args loc left related
    cases left <;> simp_all [isClos]
    all_goals first | exact .closureRec .. | exact .recRec ..

/-- Structural equality returns the same outcome on related values,
including the closure and type-error cases. This Lean-side theorem supports
the original mutual value/list equality lemma. -/
theorem doEq_related (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (left right nextLeft nextRight : Value)
    (first : vr left nextLeft) (second : vr right nextRight) :
    doEq left right = doEq nextLeft nextRight := by
  have firstView := simpleValRel_view vr simple left nextLeft first
  have secondView := simpleValRel_view vr simple right nextRight second
  cases firstView <;> cases secondView <;> try (simp only [doEq])
  case block.block tagA fieldsA targetA relA tagB fieldsB targetB relB =>
    have fieldsEq : doEqList fieldsA fieldsB = doEqList targetA targetB := by
      have worker : ∀ {as_ as' : List Value}, List.Forall₂ vr as_ as' →
          (∀ v ∈ as_, v ∈ fieldsA) → ∀ {bs bs' : List Value},
          List.Forall₂ vr bs bs' → doEqList as_ bs = doEqList as' bs' := by
        intro as_ as' related membership
        induction related with
        | nil =>
          intro bs bs' relatedB
          cases relatedB <;> simp [doEqList]
        | @cons a a' rest rest' head tail ih =>
          intro bs bs' relatedB
          cases relatedB with
          | nil => simp [doEqList]
          | @cons b b' tailB tailB' headB relatedTail =>
            have member : a ∈ fieldsA := membership a (by simp)
            have one := doEq_related vr simple a b a' b' head headB
            simp only [doEqList, ← one]
            cases doEq a b with
            | typeError => rfl
            | val flag =>
              cases flag with
              | false => rfl
              | true =>
                apply ih
                · intro v hv
                  exact membership v (by simp [hv])
                · exact relatedTail
      exact worker relA (by intro v h; exact h) relB
    simp [← relA.length_eq, ← relB.length_eq, fieldsEq]
termination_by sizeOf left
decreasing_by
  have bound := List.sizeOf_lt_of_mem member
  simp_all
  omega

/-- Equality of related lists follows from equality of each related head. -/
theorem doEqList_related (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (left right nextLeft nextRight : List Value)
    (first : List.Forall₂ vr left nextLeft) (second : List.Forall₂ vr right nextRight) :
    doEqList left right = doEqList nextLeft nextRight := by
  induction first generalizing right nextRight with
  | nil => cases second <;> simp [doEqList]
  | @cons a a' rest rest' head tail ih =>
    cases second with
    | nil => simp [doEqList]
    | @cons b b' tailB tailB' headB relatedTail =>
      have one := doEq_related vr simple a b a' b' head headB
      simp only [doEqList, ← one]
      cases doEq a b with
      | typeError => rfl
      | val flag =>
        cases flag with
        | false => rfl
        | true => exact ih _ _ relatedTail

/-- A simple value relation preserves both value equality and equality of
lists of related values. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "v_rel_do_eq"]
theorem simpleValRel_doEq (vr : Value → Value → Prop) (simple : simpleValRel vr) :
    (∀ y₁ y₂ x₁ x₂, vr x₁ y₁ ∧ vr x₂ y₂ → doEq x₁ x₂ = doEq y₁ y₂) ∧
    (∀ y₁ y₂ x₁ x₂, List.Forall₂ vr x₁ y₁ ∧ List.Forall₂ vr x₂ y₂ →
      doEqList x₁ x₂ = doEqList y₁ y₂) := by
  constructor
  · intro y₁ y₂ x₁ x₂ ⟨first, second⟩
    exact doEq_related vr simple x₁ x₂ y₁ y₂ first second
  · intro y₁ y₂ x₁ x₂ ⟨first, second⟩
    exact doEqList_related vr simple x₁ x₂ y₁ y₂ first second

end Flapjack.Compiler.Backend.ClosProps
