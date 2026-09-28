import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Exact `loopSem` `cut_state` / `cut_res` regression tests

Exercises the exact ports `LoopSemStateFiniteExact.cutState` and
`LoopSemStateFiniteExact.cutRes` (`cakeml/pancake/semantics/loopSemScript.sml:182-197`)
over the exact finite-support `loopSem$state` carrier:

* `cut_state` fails when a live key is missing from `locals`, and succeeds
  (restricting `locals` to the live keys) when the live set is contained;
* `cut_state` preserves the clock and every field except `locals`;
* `cut_res` passes a non-`NONE` result through unchanged, times out on a zero
  cut clock, and otherwise decrements the cut clock.

All state fixtures are Flapjack-specific test infrastructure and carry no
`@[hol]` tag.
-/

namespace Flapjack.Test.LoopSemCutParity

open Flapjack
open Flapjack.LoopSemStateFiniteExact

/-- A canonical `HolFfiState` with a failing oracle. -/
private def holFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }

/-- A minimal exact loopSem state with the given local map and clock. -/
private def baseState (locals : Spt (WordLocW 8)) (clock : Nat) :
    LoopSemStateFiniteExact 8 Unit :=
  { locals := locals
  , globals := HolFiniteMapExact.empty
  , memory := fun _ => .word (BitVec.ofNat 8 0)
  , mdomain := fun _ => false
  , shMdomain := fun _ => false
  , clock := clock
  , code := .ln
  , be := false
  , ffi := holFfi
  , baseAddr := 0
  , topAddr := 0 }

/-- The live set `{0}`. -/
private abbrev live0 : Spt Unit := .ls ()

/-- A local map with exactly key `0` present (value `7`). -/
private abbrev locals0 : Spt (WordLocW 8) := .ls (.word (BitVec.ofNat 8 7))

/-- The live set `{0}` is contained in a local map with key `0`. -/
private theorem subsetLive0 : sptSubsetLive live0 locals0 := by
  intro key hkey
  rw [sptMem_ls] at hkey
  rw [sptMem_ls]
  exact hkey

/-- `cut_state` succeeds when the live set is contained, restricting `locals`
    to the live keys, for any clock. -/
private theorem cutState_success (clock : Nat) :
    cutState live0 (baseState locals0 clock) =
      some { baseState locals0 clock with locals := sptInter locals0 live0 } :=
  cutState_of_subset live0 (baseState locals0 clock) (by simpa [baseState] using subsetLive0)

/-- The restriction drops nothing here: `inter {0 ↦ 7} {0}` is `{0 ↦ 7}`. -/
example : (sptInter locals0 live0 : Spt (WordLocW 8)) = locals0 := by simp [sptInter]

/-- `cut_state` fails when a live key is missing from `locals`. -/
private theorem cutState_missing :
    cutState live0 (baseState .ln 0) = none := by
  apply cutState_eq_none_of_not_subset
  intro h
  have h0 : sptMem 0 live0 := by rw [sptMem_ls]
  have hmem := h 0 h0
  simp [baseState] at hmem

/-- `cut_state` preserves the clock. -/
example (cut : LoopSemStateFiniteExact 8 Unit)
    (h : cutState live0 (baseState locals0 3) = some cut) : cut.clock = 3 := by
  have := cutState_some_clock h
  simpa [baseState] using this

/-- `cut_state` preserves every field except `locals`. -/
example (cut : LoopSemStateFiniteExact 8 Unit)
    (h : cutState live0 (baseState locals0 3) = some cut) :
    cut.globals = (baseState locals0 3).globals ∧ cut.memory = (baseState locals0 3).memory ∧
      cut.clock = (baseState locals0 3).clock ∧ cut.code = (baseState locals0 3).code ∧
      cut.ffi = (baseState locals0 3).ffi := by
  obtain ⟨hg, hm, _hmd, _hsh, hc, hcode, _hb, hffi, _hba, _hta⟩ := cutState_some_frame h
  exact ⟨hg, hm, hc, hcode, hffi⟩

/-- `cut_res` passes a non-`NONE` result through unchanged. -/
example : cutRes live0 (some (.break 2), baseState locals0 3) =
    (some (.break 2), baseState locals0 3) := rfl

/-- `cut_res` times out on a zero cut clock, emptying `locals`. -/
example : cutRes live0 (none, baseState locals0 0) =
    (some .timeOut, { baseState locals0 0 with locals := .ln }) := by
  unfold cutRes
  rw [cutState_success 0]
  rfl

/-- `cut_res` decrements the cut clock when it is positive. -/
example : cutRes live0 (none, baseState locals0 3) =
    (none, decClock { baseState locals0 3 with locals := sptInter locals0 live0 }) := by
  unfold cutRes
  rw [cutState_success 3]
  rfl

/-- `cut_res` keeps the `Error` result (and the unchanged input state) when the
    live set is not contained. -/
example : cutRes live0 (none, baseState .ln 0) =
    (some .error, baseState .ln 0) := by
  unfold cutRes
  rw [cutState_missing]

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("LoopSem cut_state restricts to live keys when contained", true),
      ("LoopSem cut_state fails on a missing live key", true),
      ("LoopSem cut_res passes non-NONE through / times out / decrements", true) ]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.LoopSemCutParity