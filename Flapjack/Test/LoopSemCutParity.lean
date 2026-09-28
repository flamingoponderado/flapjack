import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Exact `loopSem` `cut_state` / `cut_res` regression tests

Exercises the exact ports `LoopSemStateFiniteExact.cutState` and
`LoopSemStateFiniteExact.cutRes` (`cakeml/pancake/semantics/loopSemScript.sml:182-197`)
over the exact finite-support `loopSem$state` carrier.

The observation rows replay the direct HOL-EVAL fixture
`scripts/hol-probes/loop_sem_cut_zero_probe.out` (script
`loop_sem_cut_zero_probeScript.sml`), which evaluates the original HOL
`cut_state`/`cut_res` on exactly the key-`0` inputs used below:

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

/-- The live set `{0}`, matching HOL `insert 0 T LN`. -/
private abbrev live0 : Spt Unit := .ls ()

/-- A local map with key `0` present (value `5`), matching HOL
    `insert 0 (Word 5w) LN`. -/
private abbrev locals5 : Spt (WordLocW 8) := .ls (.word (BitVec.ofNat 8 5))

/-- A local map with key `0` present (value `7`). -/
private abbrev locals0 : Spt (WordLocW 8) := .ls (.word (BitVec.ofNat 8 7))

/-- A live set of one key is contained in a local map presenting that key. -/
private theorem subsetLive0 (value : WordLocW 8) :
    sptSubsetLive live0 (.ls value) := by
  intro key hkey
  rw [sptMem_ls] at hkey
  rw [sptMem_ls]
  exact hkey

/-- The empty live set is contained in any local map. -/
private theorem subsetEmpty (locals : Spt (WordLocW 8)) :
    sptSubsetLive (.ln : Spt Unit) locals := by
  intro key hkey
  exact absurd hkey (sptMem_ln key)

/-- Intersecting a leaf with a leaf keeps the left value. -/
private theorem inter_ls_ls (value : WordLocW 8) (other : Unit) :
    sptInter (.ls value) (.ls other) = .ls value := by
  simp [sptInter]

/-- Intersecting a leaf with the empty tree is empty. -/
private theorem inter_ls_ln (value : WordLocW 8) :
    sptInter (.ls value) (.ln : Spt Unit) = .ln := by
  simp [sptInter]

/-- `cut_state` succeeds when the live set is contained, restricting `locals`
    to the live keys, for any clock. -/
private theorem cutState_success {locals : Spt (WordLocW 8)}
    (h : sptSubsetLive live0 locals) (clock : Nat) :
    cutState live0 (baseState locals clock) =
      some { baseState locals clock with locals := sptInter locals live0 } :=
  cutState_of_subset live0 (baseState locals clock) (by simpa [baseState] using h)

/-- HOL `cut0_success_lookup=SOME (Word 5w)`. -/
example : (match cutState live0 (baseState locals5 7) with
    | some s' => sptLookup 0 s'.locals
    | none => none) = some (.word (BitVec.ofNat 8 5)) := by
  rw [cutState_success (subsetLive0 _) 7]
  rw [inter_ls_ls]
  rfl

/-- The restriction drops nothing here: `inter {0 ↦ 5} {0}` is `{0 ↦ 5}`. -/
example : (sptInter locals5 live0 : Spt (WordLocW 8)) = locals5 := inter_ls_ls _ _

/-- `cut_state` fails when a live key is missing from `locals`. -/
private theorem cutState_missing (clock : Nat) :
    cutState live0 (baseState .ln clock) = none := by
  apply cutState_eq_none_of_not_subset
  intro h
  have h0 : sptMem 0 live0 := by rw [sptMem_ls]
  have hmem := h 0 h0
  simp [baseState] at hmem

/-- HOL `cut0_missing=NONE`. -/
example : cutState live0 (baseState .ln 7) = none := cutState_missing 7

/-- HOL `cut0_empty_live=NONE`. -/
example : (match cutState (.ln : Spt Unit) (baseState locals5 7) with
    | some s' => sptLookup 0 s'.locals
    | none => none) = none := by
  rw [cutState_of_subset (.ln : Spt Unit) (baseState locals5 7)
        (by simpa [baseState] using subsetEmpty locals5)]
  rw [show (baseState locals5 7).locals = locals5 from rfl]
  rw [inter_ls_ln]
  rfl

/-- `cut_state` preserves the clock. -/
example (cut : LoopSemStateFiniteExact 8 Unit)
    (h : cutState live0 (baseState locals5 3) = some cut) : cut.clock = 3 := by
  have := cutState_some_clock h
  simpa [baseState] using this

/-- `cut_state` preserves every field except `locals`. -/
example (cut : LoopSemStateFiniteExact 8 Unit)
    (h : cutState live0 (baseState locals5 3) = some cut) :
    cut.globals = (baseState locals5 3).globals ∧ cut.memory = (baseState locals5 3).memory ∧
      cut.clock = (baseState locals5 3).clock ∧ cut.code = (baseState locals5 3).code ∧
      cut.ffi = (baseState locals5 3).ffi := by
  obtain ⟨hg, hm, _hmd, _hsh, hc, hcode, _hb, hffi, _hba, _hta⟩ := cutState_some_frame h
  exact ⟨hg, hm, hc, hcode, hffi⟩

/-- HOL `cut0_res_short_circuit=(SOME (Break 3),SOME (Word 5w),7)`. -/
example : (match cutRes live0 (some (.break 3), baseState locals5 7) with
    | (res, s') => (res, sptLookup 0 s'.locals, s'.clock)) =
    (some (.break 3), some (.word (BitVec.ofNat 8 5)), 7) := rfl

/-- HOL `cut0_res_missing_error=(SOME Error,NONE,7)`. -/
example : (match cutRes live0 (none, baseState .ln 7) with
    | (res, s') => (res, sptLookup 0 s'.locals, s'.clock)) =
    (some .error, none, 7) := by
  unfold cutRes
  rw [cutState_missing 7]
  rfl

/-- HOL `cut0_res_timeout=(SOME TimeOut,NONE,0)`. -/
example : (match cutRes live0 (none, baseState locals5 0) with
    | (res, s') => (res, sptLookup 0 s'.locals, s'.clock)) =
    (some .timeOut, none, 0) := by
  unfold cutRes
  rw [cutState_success (subsetLive0 _) 0]
  rw [inter_ls_ls]
  rfl

/-- HOL `cut0_res_decrement=(NONE,SOME (Word 5w),4)`. -/
example : (match cutRes live0 (none, baseState locals5 5) with
    | (res, s') => (res, sptLookup 0 s'.locals, s'.clock)) =
    (none, some (.word (BitVec.ofNat 8 5)), 4) := by
  unfold cutRes
  rw [cutState_success (subsetLive0 _) 5]
  rw [inter_ls_ls]
  rfl

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("LoopSem cut_state direct HOL rows (success / missing / empty live)", true),
      ("LoopSem cut_res direct HOL rows (short-circuit / error / timeout / decrement)", true) ]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.LoopSemCutParity