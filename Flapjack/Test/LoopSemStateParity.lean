module

public import Flapjack.Pancake.Semantics.LoopSemState
public import Flapjack.Pancake.Semantics.LoopSemStateExact

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Semantics.LoopSemState
public meta import Flapjack.Pancake.Semantics.LoopSemStateExact
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Exact `loopSem$state` carrier parity

Checks the exact width-indexed `LoopSemState` against the direct HOL oracle
`loop_sem_state_carrier_probe` (num_map locals/code, total memory, set-valued
domain, clock, be) and checks `get_var_imm` register/immediate reads on a
`LoopMachineState` with the same fields.
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

/-- Machine state with the same fields as `exactState`. -/
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
  { locals := sptInsert 0 (.word (BitVec.ofNat 8 7)) Spt.ln
  , globals := HolFiniteMapExact.empty
  , memory := fun _ => .word (BitVec.ofNat 8 0)
  , mdomain := fun _ => false
  , shMdomain := fun _ => false
  , clock := 5
  , code := Spt.ln
  , be := false
  , ffi := holTrivialFfi
  , baseAddr := 0
  , topAddr := 0 }

/-- Machine state with the same fields as `exactFiniteState`. -/
private def finiteMachineState : LoopMachineState (BitVec 8) Unit :=
  { locals := fun name => (sptLookup name exactFiniteState.locals).map loopValueOfWordLocW
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

private def exactFiniteStateCode : LoopSemStateFiniteExact 8 Unit :=
  { exactFiniteState with
    code := sptInsert 0 ([], HolLoopProg.skip) Spt.ln }

/-- Production state with the matching non-empty code table. -/
private def finiteMachineStateCode : LoopMachineState (BitVec 8) Unit :=
  { finiteMachineState with code := [(0, [], LoopProg.skip)] }

private def exactFiniteStateSeq : LoopSemStateFiniteExact 8 Unit :=
  { exactFiniteStateCode with
    code := Spt.bs Spt.ln ([], HolLoopProg.skip)
      (Spt.ls ([], HolLoopProg.seq HolLoopProg.skip HolLoopProg.tick)) }

/-- Production state with the matching two-entry code table. -/
private def finiteMachineStateSeq : LoopMachineState (BitVec 8) Unit :=
  { finiteMachineStateCode with
    code := [(0, [], LoopProg.skip), (1, [], LoopProg.seq LoopProg.skip LoopProg.tick)] }

private def finiteBridgeGuard : Bool :=
  (Flapjack.getVarImm finiteMachineState (.reg 0) ==
      some (.word (BitVec.ofNat 8 7))) &&
    (Flapjack.getVarImm finiteMachineState (.imm (BitVec.ofNat 8 9)) ==
      some (.word (BitVec.ofNat 8 9)))

#guard finiteBridgeGuard

private def finiteBridgeCodeGuard : Bool :=
  (sptLookup 0 exactFiniteStateCode.code).isSome &&
    (finiteMachineStateCode.code.length == 1)

#guard finiteBridgeCodeGuard

def runChecks : IO Bool := do
  if bridgeGuard then
    IO.println "PASS loopSem get_var_imm and memory on the machine state"
  else
    IO.println "FAIL loopSem get_var_imm and memory on the machine state"
  if finiteBridgeGuard then
    IO.println "PASS loopSem get_var_imm on the finite-support sample state"
  else
    IO.println "FAIL loopSem get_var_imm on the finite-support sample state"
  if finiteBridgeCodeGuard then
    IO.println "PASS loopSem exact finite-support non-empty code table"
  else
    IO.println "FAIL loopSem exact finite-support non-empty code table"
  pure (bridgeGuard && finiteBridgeGuard && finiteBridgeCodeGuard)

end Flapjack.Test.LoopSemStateParity