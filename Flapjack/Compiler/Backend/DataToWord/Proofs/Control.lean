import Flapjack.Compiler.Backend.Semantics.DataSem.Control

/-! Local-environment prerequisites for data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack

/-- Cutting optional live locals preserves the FFI state. The local HOL
theorem's inferred types still need a typed source replay before review. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "cut_state_opt_ffi"]
theorem cutStateOpt_ffi {C F : Type} (names : Option NumSet)
    (state next : DataSem.State C F) (run : DataSem.cutStateOpt names state = some next) :
    next.ffi = state.ffi := by
  cases names with
  | none =>
    simp [DataSem.cutStateOpt] at run
    subst next
    rfl
  | some names =>
    simp only [DataSem.cutStateOpt, DataSem.cutState] at run
    cases found : DataSem.cutEnv names state.locals with
    | none => simp [found] at run
    | some locals =>
      simp [found] at run
      subst next
      rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs
