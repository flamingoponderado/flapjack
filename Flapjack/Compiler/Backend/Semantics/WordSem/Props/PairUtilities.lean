module

public import Flapjack.HolRef

@[expose] public section

/-!
# wordProps pair utilities

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:1631-1634`
(`SND_alt_def`). HOL's `SND` is the second projection of a pair, so the
theorem restates it as the function returning the pair's second component.
-/

namespace Flapjack

/-- HOL `SND_alt_def`: the second projection of `c` is `(λ(a,b). b) c`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "SND_alt_def"]
theorem prodSndAltDef {α β : Type} (c : α × β) :
    Prod.snd c = (fun p : α × β => p.2) c := rfl

end Flapjack
