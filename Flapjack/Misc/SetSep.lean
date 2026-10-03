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

/-- Full generic commutativity, reconstructing the disjoint partition for
arbitrary predicate heaps. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "STAR_COMM"]
theorem starComm {α : Type} (p q : (α → Prop) → Prop) :
    star p q = star q p := by
  funext heap
  apply propext
  constructor <;> rintro ⟨left, right, partition, first, second⟩
  all_goals refine ⟨right, left, ⟨?_, ?_⟩, second, first⟩
  all_goals first
    | (funext entry; simpa only [or_comm] using congrFun partition.1 entry)
    | (intro entry both; exact partition.2 entry ⟨both.2, both.1⟩)

open Classical in
/-- Full generic singleton heap write. Functional graph membership derives
absence of every other payload at the written address from the original
partition; no functional-frame, finite-domain or unique-address premise is
added. The frame is preserved while the singleton payload is replaced. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "write_fun2set"]
theorem writeFun2Set {α β : Type} (newValue : α) (address : β) (oldValue : α)
    (frame : ((β × α) → Prop) → Prop) (function : β → α) (domain : β → Prop)
    (hypothesis : star (one (address, oldValue)) frame (fun2Set (function, domain))) :
    star frame (one (address, newValue))
      (fun2Set ((fun key => if key = address then newValue else function key), domain)) := by
  rcases hypothesis with ⟨head, rest, partition, singleton, frameHeap⟩
  have inHead : head (address, oldValue) := by rw [singleton]
  have oldGraph : fun2Set (function, domain) (address, oldValue) := by
    rw [← partition.1]
    exact Or.inl inHead
  have oldFacts := (fun2SetThm function domain address oldValue).mp oldGraph
  have restGraph : ∀ entry, rest entry → fun2Set (function, domain) entry := by
    intro entry member
    rw [← partition.1]
    exact Or.inr member
  have absent : ∀ value, ¬rest (address, value) := by
    intro value member
    have facts := (fun2SetThm function domain address value).mp (restGraph _ member)
    have equal : value = oldValue := facts.1.symm.trans oldFacts.1
    subst value
    exact partition.2 (address, oldValue) ⟨inHead, member⟩
  refine ⟨rest, (fun entry => entry = (address, newValue)), ⟨?_, ?_⟩, frameHeap, rfl⟩
  · funext entry
    rcases entry with ⟨key, value⟩
    apply propext
    constructor
    · rintro (member | equal)
      · have different : key ≠ address := by
          intro same
          subst key
          exact absent value member
        have facts := (fun2SetThm function domain key value).mp (restGraph _ member)
        apply (fun2SetThm _ domain key value).mpr
        exact ⟨by simpa only [different, ite_false] using facts.1, facts.2⟩
      · cases equal
        apply (fun2SetThm _ domain address newValue).mpr
        exact ⟨by simp only [ite_true], oldFacts.2⟩
    · intro member
      have facts := (fun2SetThm _ domain key value).mp member
      by_cases same : key = address
      · subst key
        have equal : newValue = value := by simpa only [ite_true] using facts.1
        exact Or.inr (congrArg (Prod.mk address) equal.symm)
      · have oldMember : fun2Set (function, domain) (key, value) :=
          (fun2SetThm function domain key value).mpr
            ⟨by simpa only [same, ite_false] using facts.1, facts.2⟩
        rw [← partition.1] at oldMember
        rcases oldMember with headMember | restMember
        · rw [singleton] at headMember
          exact (same (congrArg Prod.fst headMember)).elim
        · exact Or.inl restMember
  · rintro ⟨key, value⟩ ⟨member, equal⟩
    cases equal
    exact absent newValue member

end Flapjack.SetSep
