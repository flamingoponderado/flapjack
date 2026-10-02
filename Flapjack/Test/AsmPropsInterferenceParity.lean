import Flapjack.Compiler.Encoders.AsmProps.Interference
namespace Flapjack.Test.AsmPropsInterferenceParity
open Flapjack
example {S P : Type} (env : Nat → S → S) (proj : S → P) :
    interferenceOk env proj ↔ ∀ i ms, proj (env i ms) = proj ms := Iff.rfl
example {S P : Type} (proj : S → P) :
    interferenceOk (fun _ ms => ms) proj := by intro i ms; rfl
example : ¬ interferenceOk (fun _ ms : Nat => ms + 1) id := by
  intro h
  have bad := h 0 0
  simp at bad
end Flapjack.Test.AsmPropsInterferenceParity
