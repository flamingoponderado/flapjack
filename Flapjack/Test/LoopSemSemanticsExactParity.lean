import Flapjack.Pancake.Semantics.LoopSemStateExact.Semantics

/-!
# Exact loopSem `semantics_def` observations

Kernel-checked observations of the noncomputable exact
`LoopSemStateFiniteExact.semantics` (HOL `loopSemScript.sml:508-533`): a
program whose entry returns at once terminates successfully with no I/O, and a
missing entry fails.  Both follow from HOL's definition by the same reasoning
(HOL `EVAL` cannot compute `semantics` either).  Bead `flapjack-pxn.18.5.6.34.1`.
-/

namespace Flapjack.Test.LoopSemSemanticsExactParity

open Flapjack Flapjack.LoopSemStateFiniteExact

private def holTrivialFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
private def sRet : LoopSemStateFiniteExact 8 Unit :=
  { locals := .ln, globals := HolFiniteMapExact.empty, memory := fun _ => .word 0,
    mdomain := fun _ => false, shMdomain := fun _ => false, clock := 0,
    code := sptInsert 1 ([], .return []) .ln,
    be := false, ffi := holTrivialFfi, baseAddr := 0, topAddr := 0 }

theorem evaluate_entry (k : Nat) :
    (evaluate (.call none (some 1) [] none) { sRet with clock := k }).1 =
      if k = 0 then some .timeOut else some (.result []) := by
  rw [evaluate]
  simp [findCode, sRet, sptLookup, sptInsert]
  split
  · simp
  · rw [evaluate]; simp

theorem evaluate_entry_events (k : Nat) :
    (evaluate (.call none (some 1) [] none) { sRet with clock := k }).2.ffi.ioEvents = [] := by
  rw [evaluate]
  simp [findCode, sRet, sptLookup, sptInsert]
  split
  · rfl
  · rw [evaluate]
    simp [LoopSemStateFiniteExact.callEnv, LoopSemStateFiniteExact.decClock, holTrivialFfi]

/-- HOL-level observation: a program whose entry function `1` returns at once
    terminates successfully with no I/O, `semantics s 1 = Terminate Success []`,
    as HOL's `semantics_def` gives for the same state (at clock 0 the call times
    out, at every positive clock it returns `Result []`). -/
theorem semantics_return : semantics sRet 1 = .terminate .success [] := by
  unfold semantics
  simp only
  split
  · rename_i hc; obtain ⟨k, hk⟩ := hc; rw [evaluate_entry] at hk; split at hk <;> simp_all
  · split
    · rename_i res heq
      obtain ⟨k, t, r, outcome, he, hr, rfl⟩ := holOptionSome_some heq
      have h1 := evaluate_entry k; rw [he] at h1
      have h2 := evaluate_entry_events k; rw [he] at h2
      simp only at h1 h2
      rw [h2]
      split at h1
      · subst h1; simp at hr
      · subst h1; simp only at hr; rw [hr]
    · rename_i heq
      exfalso
      exact holOptionSome_none heq _ ⟨1, _, _, .success, rfl, by rw [evaluate_entry]; simp, rfl⟩

/-- HOL-level observation: with no code for the entry function every clock
    yields `SOME Error` (`find_code` fails), which is the `_ => T` case of HOL's
    guard, so `semantics s 1 = Fail`. -/
theorem semantics_missing_entry : semantics { sRet with code := .ln } 1 = .fail := by
  unfold semantics
  simp only
  rw [if_pos]
  refine ⟨0, ?_⟩
  rw [evaluate]
  simp [findCode, sptLookup]

def runChecks : IO Bool := do
  IO.println "PASS exact loopSem semantics_def observations (Terminate Success [] / Fail)"
  pure true

end Flapjack.Test.LoopSemSemanticsExactParity
