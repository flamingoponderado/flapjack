import Flapjack.HolRef

/-! Stateful callback adaptation used by incremental compiler passes. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- Attach configuration entries to an oracle of programs. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "syntax_to_full_oracle_def"]
def syntaxToFullOracle {Index Program Config : Type}
    (mk : (Index → Program) → Index → Config) (progs : Index → Program) (i : Index) :
    Config × Program :=
  (mk progs i, progs i)

/-- Thread the incremental compiler state through the preceding oracle entries. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "state_orac_states_def"]
def stateOracStates {S Program Output : Type} (f : S → Program → S × Output)
    (st : S) (progs : Nat → Program) : Nat → S
  | 0 => st
  | n + 1 => (f (stateOracStates f st progs n) (progs n)).1

/-- The output program produced at each incremental oracle step. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "state_co_progs_def"]
def stateCoProgs {S Program Output : Type} (f : S → Program → S × Output)
    (st : S) (orac : Nat → Program) : Nat → Output :=
  let states := stateOracStates f st orac
  fun i => (f (states i) (orac i)).2

/-- Pair the threaded states with the downstream oracle built from the outputs. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "add_state_co_def"]
def addStateCo {S Program Output Config : Type} (f : S → Program → S × Output)
    (st : S) (mk : (Nat → Output) → Nat → Config) (progs : Nat → Program) : Nat → S × Config :=
  let states := stateOracStates f st progs
  let nextProgs := stateCoProgs f st progs
  let nextOrac := mk nextProgs
  fun i => (states i, nextOrac i)

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
