import Flapjack.HolRef

/-! Counterpart of the pinned HOL set_sepScript.sml heap predicates.
Sets are represented by predicates. The function graph retains independent
address/value types and the original paired function/domain argument.
-/

namespace Flapjack.SetSep

/-- Singleton heap assertion, on arbitrary heap-element types. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "one_def"]
def one {α : Type} (element : α) : (α → Prop) → Prop :=
  fun heap => heap = (fun entry => entry = element)

/-- Empty heap assertion. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "emp_def"]
def emp {α : Type} : (α → Prop) → Prop := fun heap => heap = (fun _ => False)

/-- Pure condition, retaining HOL's required empty heap. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "cond_def"]
def cond {α : Type} (condition : Prop) : (α → Prop) → Prop :=
  fun heap => heap = (fun _ => False) ∧ condition

/-- Full paired heap partition: union equals the supplied heap, followed by
pairwise disjointness. Heaps need not be finite. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SPLIT_def"]
def split {α : Type} (heap : α → Prop) (parts : (α → Prop) × (α → Prop)) : Prop :=
  (fun entry => parts.1 entry ∨ parts.2 entry) = heap ∧
    ∀ entry, ¬ (parts.1 entry ∧ parts.2 entry)

/-- Separation conjunction over an existential disjoint partition. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "STAR_def"]
def star {α : Type} (left right : (α → Prop) → Prop) : (α → Prop) → Prop :=
  fun heap => ∃ first second, split heap (first, second) ∧ left first ∧ right second

/-- HOL's existential assertion binder; the witness type is independent of the
heap-element type, and the supplied heap is passed unchanged. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_EXISTS"]
def sepExists {α β : Type} (assertion : β → (α → Prop) → Prop) : (α → Prop) → Prop :=
  fun heap => ∃ witness, assertion witness heap

/-- Full generic function graph on the supplied domain. No finite-domain,
finite-support, injectivity, word-carrier or heap-validity premise is added. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "fun2set_def"]
def fun2Set {α β : Type} (input : (α → β) × (α → Prop)) : (α × β) → Prop :=
  fun entry => ∃ address, input.2 address ∧ entry = (address, input.1 address)

/-- Literal full generic graph membership equivalence, with the original
function-value equality preceding domain membership in the conclusion. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "fun2set_thm"]
theorem fun2SetThm {α β : Type} (function : α → β) (domain : α → Prop)
    (address : α) (value : β) :
    fun2Set (function, domain) (address, value) ↔ function address = value ∧ domain address := by
  constructor
  · rintro ⟨key, inDomain, pairEq⟩
    have keyEq : address = key := congrArg Prod.fst pairEq
    have valueEq : value = function key := congrArg Prod.snd pairEq
    subst key
    exact ⟨valueEq.symm, inDomain⟩
  · rintro ⟨valueEq, inDomain⟩
    exact ⟨address, inDomain, congrArg (Prod.mk address) valueEq.symm⟩

/-- Full separation associativity on arbitrary predicate heaps, including infinite
heaps. Both directions reconstruct the complete disjoint partition. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "STAR_ASSOC"]
theorem starAssoc {α : Type} (p q r : (α → Prop) → Prop) :
    star p (star q r) = star (star p q) r := by
  funext heap
  apply propext
  constructor
  · rintro ⟨a, bc, outer, pa, b, c, inner, qb, rc⟩
    refine ⟨(fun x => a x ∨ b x), c, ⟨?_, ?_⟩, ?_, rc⟩
    · funext x
      have outerEq := congrFun outer.1 x
      have innerEq := congrFun inner.1 x
      exact propext (by simpa only [← innerEq, or_assoc] using iff_of_eq outerEq)
    · intro x member
      rcases member.1 with ax | bx
      · apply outer.2 x
        refine ⟨ax, ?_⟩
        rw [← inner.1]
        exact Or.inr member.2
      · exact inner.2 x ⟨bx, member.2⟩
    · refine ⟨a, b, ⟨rfl, ?_⟩, pa, qb⟩
      intro x member
      apply outer.2 x
      refine ⟨member.1, ?_⟩
      rw [← inner.1]
      exact Or.inl member.2
  · rintro ⟨ab, c, outer, ⟨a, b, inner, pa, qb⟩, rc⟩
    refine ⟨a, (fun x => b x ∨ c x), ⟨?_, ?_⟩, pa, ?_⟩
    · funext x
      have outerEq := congrFun outer.1 x
      have innerEq := congrFun inner.1 x
      exact propext (by simpa only [← innerEq, or_assoc] using iff_of_eq outerEq)
    · intro x member
      rcases member.2 with bx | cx
      · exact inner.2 x ⟨member.1, bx⟩
      · apply outer.2 x
        refine ⟨?_, cx⟩
        rw [← inner.1]
        exact Or.inl member.1
    · refine ⟨b, c, ⟨rfl, ?_⟩, qb, rc⟩
      intro x member
      apply outer.2 x
      refine ⟨?_, member.2⟩
      rw [← inner.1]
      exact Or.inr member.1

end Flapjack.SetSep
