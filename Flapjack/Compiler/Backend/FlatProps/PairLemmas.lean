module

public import Flapjack.Compiler.Backend.Semantics.FlatSem

@[expose] public section

/-!
# A second-projection characterisation

Counterpart of `cakeml/compiler/backend/semantics/flatPropsScript.sml:648-652`
(`SND_SND_lemma`). HOL's `SND` is the second projection of a pair.
-/

namespace Flapjack

/-- HOL `SND_SND_lemma`: a pair's second component equals `y` exactly when the
pair can be written with `y` in second position. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "SND_SND_lemma"]
theorem prodSndEq {α β : Type} (x : α × β) (y : β) :
    x.2 = y ↔ ∃ y1 : α, x = (y1, y) := by
  constructor
  · intro h
    exact ⟨x.1, Prod.ext rfl h⟩
  · rintro ⟨y1, rfl⟩
    rfl

end Flapjack
