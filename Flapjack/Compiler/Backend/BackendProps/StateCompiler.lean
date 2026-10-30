import Flapjack.HolRef

/-! Stateful callback adaptation used by incremental compiler passes. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- Apply an incremental compiler to the state and program in each oracle entry. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "state_co_def"]
def stateCo {Index S SNext C P Q : Type} (compile : S → P → SNext × Q)
    (oracle : Index → (S × C) × P) (n : Index) : C × Q :=
  ((oracle n).1.2, (compile (oracle n).1.1 (oracle n).2).2)

/-- Stateful conversion leaves the downstream configuration unchanged. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "FST_state_co"]
theorem fst_stateCo {Index S SNext C P Q : Type} (compile : S → P → SNext × Q)
    (oracle : Index → (S × C) × P) (n : Index) :
    (stateCo compile oracle n).1 = (oracle n).1.2 := rfl

/-- Stateful conversion exposes the incremental pass's program result. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "SND_state_co"]
theorem snd_stateCo {Index S SNext C P Q : Type} (compile : S → P → SNext × Q)
    (oracle : Index → (S × C) × P) (n : Index) :
    (stateCo compile oracle n).2 = (compile (oracle n).1.1 (oracle n).2).2 := rfl

/-- Run an incremental pass before the downstream callback, threading the
pass's new state only when the downstream compiler succeeds. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "state_cc_def"]
def stateCc {S SNext C CNext P Q Code Data : Type}
    (compile : S → P → SNext × Q)
    (callback : C → Q → Option (Code × Data × CNext))
    (config : S × C) (program : P) : Option (Code × Data × SNext × CNext) :=
  let (nextState, nextProgram) := compile config.1 program
  match callback config.2 nextProgram with
  | none => none
  | some (code, data, nextConfig) => some (code, data, nextState, nextConfig)

end Flapjack.Compiler.Backend.BackendProps
