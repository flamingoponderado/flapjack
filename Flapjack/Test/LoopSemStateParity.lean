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

/-- Sample finite-support carrier with a NON-EMPTY code table: entry `0` maps to
    `([], .skip)`, matching the production code table below. This exercises the
    `prodRel` code conjunct through `loopProgExecRel` rather than the vacuous
    empty-table case. -/
private def exactFiniteStateCode : LoopSemStateFiniteExact 8 Unit :=
  { exactFiniteState with
    code := HolFiniteMapExact.empty.updateEq (0, ([], HolLoopProg.skip)) }

/-- Production state with the matching non-empty code table. -/
private def finiteMachineStateCode : LoopMachineState (BitVec 8) Unit :=
  { finiteMachineState with code := [(0, [], LoopProg.skip)] }

/-- The exact carrier with a non-empty code table satisfies `prodRel` with the
    matching production state, exercising the code conjunct through
    `loopProgExecRel`. -/
theorem finiteBridgeSampleCode :
    exactFiniteStateCode.prodRel finiteMachineStateCode := by
  unfold LoopSemStateFiniteExact.prodRel
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · intro name; rfl
  · intro global; rfl
  · intro address; rfl
  · simpa [finiteMachineStateCode, exactFiniteStateCode, finiteMachineState,
      exactFiniteState] using trivialFfiStateRel
  · intro entry hmem
    simp [finiteMachineStateCode] at hmem
    subst hmem
    refine ⟨HolLoopProg.skip, ?_, ?_⟩
    · simp [exactFiniteStateCode, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    · first | rfl | simp [loopProgExecRel]

/-- Sample finite-support carrier whose code table has a recursive-constructor
    entry, so the `prodRel` code conjunct is exercised through a non-`skip`
    `loopProgExecRel` witness (a `seq` of `skip` and `tick`) as well as the
    base `skip` entry. -/
private def exactFiniteStateSeq : LoopSemStateFiniteExact 8 Unit :=
  { exactFiniteStateCode with
    code := exactFiniteStateCode.code.updateEq
      (1, ([], HolLoopProg.seq HolLoopProg.skip HolLoopProg.tick)) }

/-- Production state with the matching two-entry code table. -/
private def finiteMachineStateSeq : LoopMachineState (BitVec 8) Unit :=
  { finiteMachineStateCode with
    code := [(0, [], LoopProg.skip), (1, [], LoopProg.seq LoopProg.skip LoopProg.tick)] }

/-- The code conjunct of `prodRel` holds for a code table containing a recursive
    constructor, through the `loopProgExecRel` introduction lemmas. -/
theorem finiteBridgeSampleSeq :
    exactFiniteStateSeq.prodRel finiteMachineStateSeq := by
  unfold LoopSemStateFiniteExact.prodRel
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · intro name; rfl
  · intro global; rfl
  · intro address; rfl
  · simpa [finiteMachineStateSeq, exactFiniteStateSeq, finiteMachineStateCode,
      exactFiniteStateCode, finiteMachineState, exactFiniteState] using trivialFfiStateRel
  · intro entry hmem
    simp only [finiteMachineStateSeq, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl
    · refine ⟨HolLoopProg.skip, ?_, ?_⟩
      · simp [exactFiniteStateSeq, exactFiniteStateCode, HolFiniteMapExact.updateEq, FUPDATE_HOL]
      · exact loopProgExecRel_skip
    · refine ⟨HolLoopProg.seq HolLoopProg.skip HolLoopProg.tick, ?_, ?_⟩
      · simp [exactFiniteStateSeq, exactFiniteStateCode, HolFiniteMapExact.updateEq, FUPDATE_HOL]
      · exact loopProgExecRel_seq loopProgExecRel_skip loopProgExecRel_tick

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

private def finiteBridgeCodeGuard : Bool :=
  (exactFiniteStateCode.code.lookup 0).isSome &&
    (finiteMachineStateCode.code.length == 1)

#guard finiteBridgeCodeGuard

def runChecks : IO Bool := do
  if bridgeGuard then
    IO.println "PASS loopSem exact state carrier fields and production state bridge"
  else
    IO.println "FAIL loopSem exact state carrier bridge"
  if finiteBridgeGuard then
    IO.println "PASS loopSem exact finite-support state production bridge"
  else
    IO.println "FAIL loopSem exact finite-support state production bridge"
  if finiteBridgeCodeGuard then
    IO.println "PASS loopSem exact finite-support non-empty code-table bridge"
  else
    IO.println "FAIL loopSem exact finite-support non-empty code-table bridge"
  pure (bridgeGuard && finiteBridgeGuard && finiteBridgeCodeGuard)

end Flapjack.Test.LoopSemStateParity