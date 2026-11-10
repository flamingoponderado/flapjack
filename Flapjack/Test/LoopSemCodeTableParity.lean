module

public import Flapjack.Pancake.Semantics.LoopSemStateExact

-- Checks below run compiled code from these modules.
public meta import Flapjack.LoopCallEnv
public meta import Flapjack.Pancake.Semantics.LoopSemStateExact
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Loop code-table lookup regressions

Regression tests for `lookupLoopFunction`/`findLoopCode` over an association
list code table and the exact-shaped `findLoopCodeSpt`.  They exercise

* a multi-entry code table (labels `0` and `1`) whose association list
  repeats label `1`, so `lookupLoopFunction`'s first-occurrence-wins order is
  exercised;
* the missing-entry case, where an absent exact `sptLookup` and an absent
  association-list entry both make `find_code` fail; and
* the link (`none` label) `find_code` case with a trailing `.loc _ 0`
  argument.

All declarations here are Flapjack-specific test infrastructure and carry no
`@[hol]` tag.
-/

namespace Flapjack.Test.LoopSemCodeTableParity

open Flapjack

private abbrev W := BitVec 8

/-- Tag identifying the callee body so tests can distinguish table entries
    without needing a `BEq (LoopProg W)` instance. -/
private def loopBodyTag : LoopProg W → Nat
  | .mark _ => 1
  | .tick => 2
  | _ => 0

/-- A canonical `HolFfiState` with a failing oracle. -/
private def holFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }

/-- `trivialFfiState Unit ()` is `FfiStateRel`-related to `holFfi`. -/
private theorem ffiRel : FfiStateRel (trivialFfiState Unit ()) holFfi := by
  unfold FfiStateRel
  refine ⟨rfl, ?_, ?_⟩
  · simp [trivialFfiState, holFfi, FfiEventListRel]
  · intro name holName hname state configuration holConfiguration bytes holBytes hconf hbytes
    simp [trivialFfiState, holFfi, OracleResultRel, OutcomeRel]

/-- Fixed non-code fields of the sample exact carrier. -/
private def exactBase : LoopSemStateFiniteExact 8 Unit :=
  { locals := sptInsert 0 (.word (BitVec.ofNat 8 7)) Spt.ln
  , globals := HolFiniteMapExact.empty
  , memory := fun _ => .word (BitVec.ofNat 8 0)
  , mdomain := fun _ => false
  , shMdomain := fun _ => false
  , clock := 5
  , code := Spt.ln
  , be := false
  , ffi := holFfi
  , baseAddr := 0
  , topAddr := 0 }

/-- Machine state derived field-for-field from an exact state, with a
    caller-supplied code table. -/
private def machineOf (s : LoopSemStateFiniteExact 8 Unit) (code : LoopCode W) :
    LoopMachineState W Unit :=
  { locals := fun name => (sptLookup name s.locals).map loopValueOfWordLocW
  , globals := fun global => (s.globals.lookup global).map loopValueOfWordLocW
  , memory := fun address => some (loopValueOfWordLocW (s.memory address))
  , mdomain := s.mdomain
  , shMdomain := s.shMdomain
  , clock := s.clock
  , code := code
  , be := s.be
  , ffi := trivialFfiState Unit ()
  , baseAddr := s.baseAddr
  , topAddr := s.topAddr }

private def exactMulti : LoopSemStateFiniteExact 8 Unit :=
  { exactBase with
    code := Spt.bs Spt.ln ([0, 2], HolLoopProg.skip) (Spt.ls ([7], HolLoopProg.tick)) }

/-- Matching production association list; label `1` is repeated so the
    first-occurrence-wins order of `lookupLoopFunction` is exercised. -/
private def multiCode : LoopCode W :=
  [(0, [0, 2], LoopProg.skip), (1, [7], LoopProg.tick), (1, [7], LoopProg.tick)]

private theorem multiForward :
    ∀ entry, entry ∈ multiCode →
      ∃ program, sptLookup entry.1 exactMulti.code = some (entry.2.1, program) ∧
        loopProgExecRel entry.2.2 program := by
  intro entry hentry
  simp only [multiCode, List.mem_cons, List.mem_nil_iff, or_false] at hentry
  rcases hentry with rfl | rfl | rfl
  · exact ⟨HolLoopProg.skip,
      by simp [exactMulti, exactBase, sptLookup], loopProgExecRel_skip⟩
  · exact ⟨HolLoopProg.tick,
      by simp [exactMulti, exactBase, sptLookup], loopProgExecRel_tick⟩
  · exact ⟨HolLoopProg.tick,
      by simp [exactMulti, exactBase, sptLookup], loopProgExecRel_tick⟩

example : sptLookup 0 exactMulti.code = some ([0, 2], HolLoopProg.skip) := by
  simp [exactMulti, exactBase, sptLookup]

/-- The production lookup of label `1` returns the FIRST duplicate entry. -/
example : lookupLoopFunction 1 multiCode = some ([7], LoopProg.tick) := rfl

/-- The production lookup of an absent label fails. -/
example : lookupLoopFunction 9 multiCode = none := rfl

example : (findLoopCode (some 1) [.word 7] multiCode).isSome = true := rfl

/-! ## Missing-entry case -/

/-- An absent exact label keeps the production lookup absent. -/
example : lookupLoopFunction 9 multiCode = none := rfl

example : sptLookup 9 exactMulti.code = none := by
  simp [exactMulti, exactBase, sptLookup]

example : (findLoopCode (some 9) [] multiCode).isNone = true := rfl

/-! ## Link (`none` label) case -/

private def linkEnvCheck : Bool :=
  match findLoopCode none [.word 5, .loc 1 0] multiCode with
  | some (env, body) =>
      (env 7 == some (.word 5)) && (loopBodyTag body == loopBodyTag LoopProg.tick)
  | none => false

#guard linkEnvCheck

/-! ## Pure first-occurrence-wins regression

An independent production-only table where the two duplicate entries have
different parameter lists; the earlier entry must win. -/
private def dupCode : LoopCode W := [(3, [9], LoopProg.tick), (3, [8], LoopProg.skip)]

private def dupFirstWins : Bool :=
  match lookupLoopFunction 3 dupCode with
  | some (params, _) => params == [9]
  | none => false

#guard dupFirstWins

/-- The exact sample has a non-empty two-entry code table. -/
example : (sptLookup 0 exactMulti.code).isSome = true := rfl

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("LoopSem code table duplicate-label first-occurrence wins", dupFirstWins),
      ("LoopSem code table link binds callee parameters", linkEnvCheck) ]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.LoopSemCodeTableParity
