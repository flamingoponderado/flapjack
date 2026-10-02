import Flapjack.HolRef

/-! Counterpart of the pinned HOL set_sepScript.sml heap predicates.
Sets are represented by predicates. The function graph retains independent
address/value types and the original paired function/domain argument.
-/

namespace Flapjack.SetSep

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

end Flapjack.SetSep
