import Flapjack.Pancake.CrepToLoop.Proofs.CrepNonFailStartLookup
import Flapjack.Pancake.Semantics.CrepSem.CrepObservationalSemantics

/-!
# Concrete regression for `crepSemantics_ne_fail_imp_holAlookup`

A single concrete non-`Fail` instance: an exact Crep state whose `start` entry is
`([], Return [])`.  The entry `Call NONE start []` at clock `0` returns
`TimeOut` and at every positive clock returns `Return []`, so the wrapper's
result map never yields `RunError`; the semantics is therefore not `Fail`, and
the lemma must recover the start entry.  The fixture has no `@[hol]` tag; it is a
Flapjack-specific kernel-checked regression.
-/

namespace Flapjack.Test.CrepSemNonFailStartLookupParity

open Flapjack Flapjack.Basis.Pure.MlString

private abbrev MlS := MlString

private def startName : MlS := ofString "start"

private def code : List (MlS × List Nat × CrepProgHOL 8) :=
  [(startName, ([], CrepProgHOL.return []))]

private def st : CrepSemHOLState 8 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := alistToFmapCodeExact code
  memory := fun _ => HolWordLab.word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 0
  be := false
  ffi := initialHolFfiState (fun _ _ _ _ => .final .failed) ()
  baseAddr := 0
  topAddr := 0

/-- The concrete alist-to-`ALOOKUP` check pins the start entry. -/
private example : holAlookup code startName = some ([], CrepProgHOL.return []) := by
  simp [code, holAlookup]

private theorem st_code_lookup :
    st.code.lookup startName = some ([], CrepProgHOL.return []) := by
  simp [st, code, alistToFmapCodeExact, HolFiniteMapExact.lookup_updateList,
    FUPDATE_LIST, FUPDATE]

/-- The concrete state's entry semantics is not `Fail`: the clock-`0` entry call
returns `TimeOut` and every positive-clock call returns `Return []`, so the
wrapper's result map is never `RunError`. -/
private theorem st_no_fail : crepSemantics st startName ≠ .fail := by
  rw [crepSemIsWrapper]
  apply crepToLoopSemanticsWrapper_ne_fail_of_no_error
  rintro ⟨k, v, hk⟩
  simp only [Function.comp_apply, Prod.map] at hk
  cases k with
  | zero =>
      simp only [st_code_lookup, evalCrepSemHOLProgExact_call] at hk
      cases hk
  | succ k =>
      simp [st_code_lookup, evalCrepSemHOLProgExact_call_holShape, lookupCodeFiniteHOL,
        evalCrepSemHOLProgExact_return, crepReturnInfoNodupError, Option.pure_def] at hk

/-- The concrete instance: the kernel-checked regression required by the bead.
A concrete non-`Fail` exact Crep semantics yields the start-code lookup, and the
recovered entry is pinned to `([], Return [])`. -/
example : ∃ prog, holAlookup code startName = some ([], prog) ∧
    prog = CrepProgHOL.return [] := by
  obtain ⟨prog, hprog⟩ :=
    crepSemantics_ne_fail_imp_holAlookup st code startName rfl rfl (by simp [code])
      st_no_fail
  exact ⟨prog, hprog, by simpa [code, holAlookup] using hprog.symm⟩

end Flapjack.Test.CrepSemNonFailStartLookupParity
