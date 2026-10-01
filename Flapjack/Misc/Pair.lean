import Flapjack.HolRef

/-!
# HOL pair lexicographic order `LEX`

Exact port of `HOL/src/coretypes/pairScript.sml` `LEX_DEF` (786-791), cited in
the pinned upstream HOL submodule. HOL relations `'a -> 'a -> bool` are
rendered as `α → α → Prop`; the paired abstraction `\(s,t) (u,v). ...` reads
the components `p.1`, `p.2` (HOL `UNCURRY`).
-/

namespace Flapjack

/-- Exact HOL `LEX_DEF` (`pairScript.sml:786-791`):
`(R1 LEX R2) = \(s,t) (u,v). R1 s u \/ (s = u) /\ R2 t v`. -/
@[hol "HOL/src/coretypes/pairScript.sml" "LEX_DEF"]
def holLex {α β : Type} (R1 : α → α → Prop) (R2 : β → β → Prop) (p q : α × β) : Prop :=
  R1 p.1 q.1 ∨ (p.1 = q.1 ∧ R2 p.2 q.2)

instance {α β : Type} {R1 : α → α → Prop} {R2 : β → β → Prop} [DecidableEq α]
    [∀ a b, Decidable (R1 a b)] [∀ a b, Decidable (R2 a b)] (p q : α × β) :
    Decidable (holLex R1 R2 p q) :=
  inferInstanceAs (Decidable (R1 p.1 q.1 ∨ (p.1 = q.1 ∧ R2 p.2 q.2)))

end Flapjack
