import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Two-way `LoopSem` code-table production bridge

Regression tests for the reverse/coverage direction added to
`LoopSemStateFiniteExact.prodRel` together with the exact-shaped
`findLoopCodeSpt`.  They exercise

* a multi-entry code table (labels `0` and `1`) whose production
  association list repeats label `1`, so `lookupLoopFunction`'s
  first-occurrence-wins order is exercised;
* the missing-entry case, where an absent exact `sptLookup` keeps the
  production lookup absent and both `find_code` readings fail; and
* the link (`none` label) `find_code` case with a trailing `.loc _ 0`
  argument.

All declarations here are Flapjack-specific bridge infrastructure and carry no
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

/-- Production state derived field-for-field from an exact state, with a
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

/-- Assemble `prodRel` for a `machineOf` state from the two code-table
    directions; the non-code fields hold by construction. -/
private theorem prodRel_machineOf (s : LoopSemStateFiniteExact 8 Unit)
    (code : LoopCode W) (hffi : FfiStateRel (trivialFfiState Unit ()) s.ffi)
    (hforward : ∀ entry, entry ∈ code →
      ∃ program, sptLookup entry.1 s.code = some (entry.2.1, program) ∧
        loopProgExecRel entry.2.2 program)
    (hcov : LoopCodeTableCoverage s (machineOf s code)) :
    s.prodRel (machineOf s code) := by
  unfold LoopSemStateFiniteExact.prodRel
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl, hforward, hcov⟩
  · intro name; rfl
  · intro global; rfl
  · intro address; rfl
  · simpa [machineOf] using hffi

/-! ## Multi-entry table with a duplicate label

The exact code is the literal well-formed tree
`BS LN ([0, 2], skip) (LS ([7], tick))`, whose support is exactly `{0, 1}`. -/

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

private theorem multiCoverage :
    LoopCodeTableCoverage exactMulti (machineOf exactMulti multiCode) := by
  intro label parameters program hlookup
  by_cases h0 : label = 0
  · subst h0
    have hpair : ([0, 2], HolLoopProg.skip) = (parameters, program) := by
      simpa [exactMulti, exactBase, sptLookup] using hlookup
    have hfst : ([0, 2] : List Nat) = parameters := congrArg Prod.fst hpair
    have hsnd : HolLoopProg.skip = program := congrArg Prod.snd hpair
    exact ⟨(0, [0, 2], LoopProg.skip), by simp [machineOf, multiCode], rfl, hfst,
      by rw [← hsnd]; exact loopProgExecRel_skip⟩
  · by_cases h1 : label = 1
    · subst h1
      have hpair : ([7], HolLoopProg.tick) = (parameters, program) := by
        simpa [exactMulti, exactBase, sptLookup] using hlookup
      have hfst : ([7] : List Nat) = parameters := congrArg Prod.fst hpair
      have hsnd : HolLoopProg.tick = program := congrArg Prod.snd hpair
      exact ⟨(1, [7], LoopProg.tick), by simp [machineOf, multiCode], rfl, hfst,
        by rw [← hsnd]; exact loopProgExecRel_tick⟩
    · have hnone : sptLookup label exactMulti.code = none := by
        simp only [exactMulti, exactBase, sptLookup]
        split <;> simp_all <;> omega
      rw [hnone] at hlookup
      exact absurd hlookup (by simp)

private theorem multiBridge : exactMulti.prodRel (machineOf exactMulti multiCode) :=
  prodRel_machineOf exactMulti multiCode ffiRel multiForward multiCoverage

/-- The exact lookup of label `0` is the faithful `skip` entry. -/
example : sptLookup 0 exactMulti.code = some ([0, 2], HolLoopProg.skip) := by
  simp [exactMulti, exactBase, sptLookup]

/-- The production lookup of label `1` returns the FIRST duplicate entry. -/
example : lookupLoopFunction 1 multiCode = some ([7], LoopProg.tick) := rfl

/-- The production lookup of an absent label fails. -/
example : lookupLoopFunction 9 multiCode = none := rfl

/-- The two-way theorem gives the first-occurrence-wins production lookup
    `loopProgExecRel`-related to the exact faithful program. -/
example : ∃ executableProgram,
    lookupLoopFunction 1 multiCode = some ([7], executableProgram) ∧
      loopProgExecRel executableProgram HolLoopProg.tick :=
  LoopSemStateFiniteExact.lookupLoopFunction_eq_of_prodRel multiBridge
    (by simp [exactMulti, exactBase, sptLookup])

/-- The full `find_code` correspondence for the labelled duplicate case. -/
example : loopFindCodeResultRel
    (findLoopCode (some 1) [.word 7] multiCode)
    (findLoopCodeSpt (some 1) [.word 7] exactMulti.code) :=
  LoopSemStateFiniteExact.findLoopCode_prodRel multiBridge (some 1) [.word 7]

/-- The production labelled lookup yields the first duplicate with the bound
    parameters and the `tick` body. -/
example : (findLoopCode (some 1) [.word 7] multiCode).isSome = true := rfl

/-! ## Missing-entry case -/

/-- An absent exact label keeps the production lookup absent. -/
example : lookupLoopFunction 9 multiCode = none := rfl

example : sptLookup 9 exactMulti.code = none := by
  simp [exactMulti, exactBase, sptLookup]

/-- Both `find_code` readings fail on the absent label `9`. -/
example : loopFindCodeResultRel
    (findLoopCode (some 9) [] multiCode)
    (findLoopCodeSpt (some 9) [] exactMulti.code) :=
  LoopSemStateFiniteExact.findLoopCode_prodRel multiBridge (some 9) []

example : (findLoopCode (some 9) [] multiCode).isNone = true := rfl

/-! ## Link (`none` label) case -/

/-- The link form looks up the trailing `.loc 1 0` and binds the leading
    arguments to the callee parameters. -/
example : loopFindCodeResultRel
    (findLoopCode none [.word 5, .loc 1 0] multiCode)
    (findLoopCodeSpt none [.word 5, .loc 1 0] exactMulti.code) :=
  LoopSemStateFiniteExact.findLoopCode_prodRel multiBridge none [.word 5, .loc 1 0]

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

/-- The `prodRel` sample itself is non-vacuous: it has a non-empty two-entry
    exact code table. -/
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
