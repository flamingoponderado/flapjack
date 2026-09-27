import Flapjack.Pancake.Semantics.LoopSemState
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Exact `loopSem$state` carrier parity

Checks the exact width-indexed `LoopSemState` against the direct HOL oracle
`loop_sem_state_carrier_probe` (num_map locals/code, total memory, set-valued
domain, clock, be) and exercises the observational bridge to the production
`LoopMachineState` including `get_var_imm` register/immediate reads.
-/

namespace Flapjack.Test.LoopSemStateParity

open Flapjack

private abbrev W := BitVec 8

/-- Sample exact carrier mirroring the HOL probe's `s1`. -/
private def exactState : LoopSemState 8 Unit :=
  { locals := fun name => if name = 0 then some (.word (BitVec.ofNat 8 7)) else none
  , globals := fun _ => none
  , memory := fun _ => .word (BitVec.ofNat 8 0)
  , mdomain := fun _ => false
  , shMdomain := fun _ => false
  , clock := 5
  , code := fun _ => none
  , be := false
  , ffi := trivialFfiState Unit ()
  , baseAddr := 0
  , topAddr := 0 }

/-- Production state satisfying the bridge for `exactState`. -/
private def machineState : LoopMachineState W Unit :=
  { locals := fun name => (exactState.locals name).map loopValueOfWordLocW
  , globals := fun global => (exactState.globals global).map loopValueOfWordLocW
  , memory := fun address => some (loopValueOfWordLocW (exactState.memory address))
  , mdomain := exactState.mdomain
  , shMdomain := exactState.shMdomain
  , clock := exactState.clock
  , code := []
  , be := exactState.be
  , ffi := exactState.ffi
  , baseAddr := exactState.baseAddr
  , topAddr := exactState.topAddr }

/-- The exact carrier's memory is total, so every production cell is present. -/
example : machineState.memory (3 : W) = some (.word (BitVec.ofNat 8 0)) := rfl

/-- Rows matching the HOL oracle. -/
example : exactState.locals 0 = some (.word (BitVec.ofNat 8 7)) := rfl
example : exactState.locals 1 = none := rfl
example : exactState.memory (3 : W) = .word (BitVec.ofNat 8 0) := rfl
example : exactState.mdomain (3 : W) = false := rfl
example : exactState.clock = 5 := rfl
example : exactState.code 0 = none := rfl
example : exactState.be = false := rfl

theorem bridgeSample : LoopMachineStateRel exactState machineState := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro name
    simp [machineState]
  · intro global
    simp [machineState]
  · intro address
    simp [machineState]
  · intro entry hmem
    simp [machineState] at hmem

/-- Register read through the bridge. -/
example : getVarImm machineState (.reg 0) = some (.word (BitVec.ofNat 8 7)) := by
  rw [getVarImm_reg_eq_of_loopMachineStateRel bridgeSample 0]
  rfl

/-- Immediate read through the bridge. -/
example : getVarImm machineState (.imm (BitVec.ofNat 8 9)) =
    some (.word (BitVec.ofNat 8 9)) :=
  getVarImm_imm_eq_of_loopMachineStateRel bridgeSample (BitVec.ofNat 8 9)

private def bridgeGuard : Bool :=
  (getVarImm machineState (.reg 0) == some (.word (BitVec.ofNat 8 7))) &&
    (getVarImm machineState (.imm (BitVec.ofNat 8 9)) ==
      some (.word (BitVec.ofNat 8 9))) &&
    (machineState.memory (3 : W) == some (.word (BitVec.ofNat 8 0)))

#guard bridgeGuard

/-- Carrier-level register read and clock-independence. -/
example : LoopSemState.getVarImm (.reg 0) exactState =
    some (.word (BitVec.ofNat 8 7)) := rfl

example : LoopSemState.getVarImm (.reg 0) { exactState with clock := 9 } =
    LoopSemState.getVarImm (.reg 0) exactState :=
  LoopSemState.getVarImm_clock (.reg 0) exactState 9

/-- Carrier-level `get_vars` and clock-independence. -/
example : LoopSemState.getVars [0] exactState =
    some [.word (BitVec.ofNat 8 7)] := rfl

example : LoopSemState.getVars [0, 1] exactState = none := rfl

example : LoopSemState.getVars [0] { exactState with clock := 9 } =
    LoopSemState.getVars [0] exactState :=
  LoopSemState.getVars_clock [0] exactState 9

/-- Exact carrier `get_var_imm` maps to the production read under the bridge. -/
example : (LoopSemState.getVarImm (.reg 0) exactState).map loopValueOfWordLocW =
    getVarImm machineState (.reg 0) :=
  LoopSemState.getVarImm_map_eq_of_loopMachineStateRel bridgeSample (.reg 0)

/-! ## Exact finite-support carrier (`LoopSemStateFiniteExact`) production bridge -/

/-- A canonical `HolFfiState` with a failing oracle, related to
    `trivialFfiState Unit ()`. -/
private def holTrivialFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }

/-- `trivialFfiState Unit ()` is `FfiStateRel`-related to `holTrivialFfi`. -/
private theorem trivialFfiStateRel :
    FfiStateRel (trivialFfiState Unit ()) holTrivialFfi := by
  unfold FfiStateRel
  refine ⟨rfl, ?_, ?_⟩
  · simp [trivialFfiState, holTrivialFfi, FfiEventListRel]
  · intro name holName hname state configuration holConfiguration bytes holBytes hconf hbytes
    simp [trivialFfiState, holTrivialFfi, OracleResultRel, OutcomeRel]

/-- Sample finite-support carrier: local `0 ↦ Word 7`, all else empty. -/
private def exactFiniteState : LoopSemStateFiniteExact 8 Unit :=
  { locals := HolFiniteMapExact.empty.updateEq (0, .word (BitVec.ofNat 8 7))
  , globals := HolFiniteMapExact.empty
  , memory := fun _ => .word (BitVec.ofNat 8 0)
  , mdomain := fun _ => false
  , shMdomain := fun _ => false
  , clock := 5
  , code := HolFiniteMapExact.empty
  , be := false
  , ffi := holTrivialFfi
  , baseAddr := 0
  , topAddr := 0 }

/-- Production state satisfying `prodRel` for `exactFiniteState`. -/
private def finiteMachineState : LoopMachineState (BitVec 8) Unit :=
  { locals := fun name => (exactFiniteState.locals.lookup name).map loopValueOfWordLocW
  , globals := fun global => (exactFiniteState.globals.lookup global).map loopValueOfWordLocW
  , memory := fun address => some (loopValueOfWordLocW (exactFiniteState.memory address))
  , mdomain := exactFiniteState.mdomain
  , shMdomain := exactFiniteState.shMdomain
  , clock := exactFiniteState.clock
  , code := []
  , be := exactFiniteState.be
  , ffi := trivialFfiState Unit ()
  , baseAddr := exactFiniteState.baseAddr
  , topAddr := exactFiniteState.topAddr }

/-- The exact finite-support carrier satisfies `prodRel` with the sample
    production state (empty code makes the code conjunct vacuous). -/
theorem finiteBridgeSample : exactFiniteState.prodRel finiteMachineState := by
  unfold LoopSemStateFiniteExact.prodRel
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · intro name; rfl
  · intro global; rfl
  · intro address; rfl
  · simpa [finiteMachineState, exactFiniteState] using trivialFfiStateRel
  · intro entry hmem; simp [finiteMachineState] at hmem

/-- Register read on the exact carrier transports to the production read. -/
example : Flapjack.getVarImm finiteMachineState (.reg 0) =
    some (.word (BitVec.ofNat 8 7)) := by
  rw [← LoopSemStateFiniteExact.getVarImm_map_eq_of_prodRel finiteBridgeSample (.reg 0)]
  rfl

/-- Immediate read on the exact carrier transports to the production read. -/
example : Flapjack.getVarImm finiteMachineState (.imm (BitVec.ofNat 8 9)) =
    some (.word (BitVec.ofNat 8 9)) :=
  LoopSemStateFiniteExact.getVarImm_map_eq_of_prodRel finiteBridgeSample
    (.imm (BitVec.ofNat 8 9))

/-- Recursive `get_vars` transports to the production read. -/
example : Flapjack.getVars [0] finiteMachineState =
    some [.word (BitVec.ofNat 8 7)] := by
  rw [← LoopSemStateFiniteExact.getVars_map_eq_of_prodRel finiteBridgeSample [0]]
  rfl

/-- A missing local makes the recursive read fail on both sides. -/
example : Flapjack.getVars [0, 1] finiteMachineState = none := by
  rw [← LoopSemStateFiniteExact.getVars_map_eq_of_prodRel finiteBridgeSample [0, 1]]
  rfl

private def finiteBridgeGuard : Bool :=
  (Flapjack.getVarImm finiteMachineState (.reg 0) ==
      some (.word (BitVec.ofNat 8 7))) &&
    (Flapjack.getVarImm finiteMachineState (.imm (BitVec.ofNat 8 9)) ==
      some (.word (BitVec.ofNat 8 9)))

#guard finiteBridgeGuard

def runChecks : IO Bool := do
  if bridgeGuard then
    IO.println "PASS loopSem exact state carrier fields and production state bridge"
  else
    IO.println "FAIL loopSem exact state carrier bridge"
  if finiteBridgeGuard then
    IO.println "PASS loopSem exact finite-support state production bridge"
  else
    IO.println "FAIL loopSem exact finite-support state production bridge"
  pure (bridgeGuard && finiteBridgeGuard)

end Flapjack.Test.LoopSemStateParity