import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Aesop
/-! Shared non-FFI facts for resource and safety proofs. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL
set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
/-- Flapjack helper for the HOL `do_app_aux_safe_peak_swap` family and the
`do_app_io_events_mono` and `do_app_safe_for_space_mono` proofs: successful
non-FFI applications preserve FFI state and safety monotonicity, and remain
successful under an arbitrary safety update. -/
theorem applyNonFfi_successFields {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state next : State C F) (value : Value) (safe : Bool)
    (run : applyNonFfi op values state = some (value, next)) :
    (∃ safe', applyNonFfi op values {state with safeForSpace := safe} =
      some (value, {next with safeForSpace := safe'})) ∧
    next.ffi = state.ffi ∧ (next.safeForSpace = true → state.safeForSpace = true) := by
  simp only [applyNonFfi, Option.bind] at run ⊢
  all_goals repeat' (first | split at run | split) <;> simp_all [withFreshTimestamp, checkLim, Option.bind]
  all_goals try (aesop (config := {warnOnNonterminal := false}))
  all_goals cases safe <;> (simp; try omega)
end Flapjack.Compiler.Backend.DataSem
