import Flapjack.Misc.LList

/-!
# HOL `lprefix_lub` (least upper bounds of lazy-list prefix chains)

Untagged rendering of HOL4's `examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml`
(HOL library, outside the CakeML submodule, so no `@[hol]` tags), plus HOL's
option-choice binder `some` (`HOL/src/coretypes/optionScript.sml:794`).  HOL sets
`'a llist set` are rendered as predicates `HolLList α → Prop`.  These are the
ingredients of the Pancake observational `semantics_def`s
(`build_lprefix_lub (IMAGE ... UNIV)`).  Noncomputable exactly where HOL uses
Hilbert choice.
-/

namespace Flapjack

open Classical in
/-- HOL `some P = if ?x. P x then SOME (@x. P x) else NONE`
    (`optionScript.sml:794-796`); under the guard, `Classical.choose` is a
    witness of `P` exactly as HOL's `@x. P x`. -/
noncomputable def holOptionSome {α : Type} (P : α → Prop) : Option α :=
  if h : ∃ x, P x then some (Classical.choose h) else none

theorem holOptionSome_some {α : Type} {P : α → Prop} {x : α}
    (h : holOptionSome P = some x) : P x := by
  unfold holOptionSome at h
  split at h
  · rename_i hex; cases h; exact Classical.choose_spec hex
  · cases h

theorem holOptionSome_none {α : Type} {P : α → Prop}
    (h : holOptionSome P = none) : ∀ x, ¬ P x := by
  unfold holOptionSome at h
  split at h
  · cases h
  · rename_i hn; exact fun x hx => hn ⟨x, hx⟩

namespace HolLList

variable {α : Type}

/-- HOL `lprefix_chain ls ⇔ !ll1 ll2. ll1 ∈ ls ∧ ll2 ∈ ls ⇒ LPREFIX ll1 ll2 ∨ LPREFIX ll2 ll1`
    (`lprefix_lubScript.sml:171-174`). -/
def lprefixChain (ls : HolLList α → Prop) : Prop :=
  ∀ ll1 ll2, ls ll1 → ls ll2 → lprefix ll1 ll2 ∨ lprefix ll2 ll1

/-- HOL `lprefix_chain_nth n ls = some x. ?l. l ∈ ls ∧ LNTH n l = SOME x`
    (`lprefix_lubScript.sml:200-203`). -/
noncomputable def lprefixChainNth (n : Nat) (ls : HolLList α → Prop) : Option α :=
  holOptionSome (fun x => ∃ l, ls l ∧ lnth n l = some x)

/-- HOL `lprefix_lub ls lub ⇔ (!ll. ll ∈ ls ⇒ LPREFIX ll lub) ∧
    (∀ub. (!ll. ll ∈ ls ⇒ LPREFIX ll ub) ⇒ LPREFIX lub ub)` (`lprefix_lubScript.sml:306-310`). -/
def lprefixLub (ls : HolLList α → Prop) (lub : HolLList α) : Prop :=
  (∀ ll, ls ll → lprefix ll lub) ∧ (∀ ub, (∀ ll, ls ll → lprefix ll ub) → lprefix lub ub)

/-- HOL `build_lprefix_lub_f ls n = OPTION_MAP (λx. (n+1, x)) (lprefix_chain_nth n ls)`
    (`lprefix_lubScript.sml:430-433`). -/
noncomputable def buildLprefixLubF (ls : HolLList α → Prop) (n : Nat) : Option (Nat × α) :=
  (lprefixChainNth n ls).map (fun x => (n + 1, x))

/-- HOL `build_lprefix_lub ls = LUNFOLD (build_lprefix_lub_f ls) 0`
    (`lprefix_lubScript.sml:435-438`). -/
noncomputable def buildLprefixLub (ls : HolLList α → Prop) : HolLList α :=
  lunfold (buildLprefixLubF ls) 0

end HolLList

end Flapjack
