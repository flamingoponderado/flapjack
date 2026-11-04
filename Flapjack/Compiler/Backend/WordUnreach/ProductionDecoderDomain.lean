import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Pancake.LoopToWord

/-! Flapjack-only representation infrastructure for the executed Word decoder.
The native unreachable-code pass retains instruction leaves, so it cannot
introduce an unsupported instruction into a decoder-accepted program. These
are codec-domain facts, not HOL pass-correctness ports or evaluation premises.
-/

namespace Flapjack.Compiler.Backend.WordUnreach

open Flapjack

private theorem pairDomain {α β γ : Type} (first : Option α)
    (second : Option β) (make : α → β → γ) :
    (first.bind fun a => second.bind fun b => some (make a b)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

private theorem mapDomain {α β : Type} (value : Option α) (make : α → β) :
    (value.bind fun a => some (make a)).isSome = value.isSome := by
  cases value <;> rfl

end Flapjack.Compiler.Backend.WordUnreach
