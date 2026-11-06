import Flapjack.Compiler.Backend.Semantics.BvlSem.Call
import Flapjack.HolRef
import Mathlib.Data.List.Infix
import Aesop

/-! Properties of BVL call-code lookup. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem

namespace FindCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end FindCarrier

/-- Successful lookup passes either the entire argument list or its prefix. -/
theorem findCode_args_subset {α : Type} (dest : Option Nat) (args output : List Value)
    (code : Spt (Nat × α)) (body : α) (run : findCode dest args code = some (output, body)) :
    ∀ value ∈ output, value ∈ args := by
  unfold findCode at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop (add safe List.mem_of_mem_dropLast)

/-- Every property of the supplied arguments holds of the selected ones. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "find_code_EVERY_IMP"
  (fmap_as_finite_support := [refs])]
theorem findCodeEveryImp {C F : Type} (dest : Option Nat) (args : List Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (output : List Value) (body : Bvl.Exp)
    (predicate : Value → Prop) (run : findCode dest args state.code = some (output, body))
    (all : ∀ value ∈ args, predicate value) : ∀ value ∈ output, predicate value := by
  intro value member
  exact all value (findCode_args_subset dest args output state.code body run value member)

end Flapjack.Compiler.Backend.BvlProps
