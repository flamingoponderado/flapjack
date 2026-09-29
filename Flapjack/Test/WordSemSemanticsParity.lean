import Flapjack.Compiler.Backend.Semantics.WordSem.Semantics

/-!
# Exact wordSem `semantics_def` observations

These are kernel-checked observations of the noncomputable exact
`WordSemStateFiniteExact.semantics` (HOL `wordSemScript.sml:1374-1401`), for
the entry call `Call NONE (SOME 5) [0] NONE`:
* an entry function `5` that returns `Loc 1 0` at once terminates successfully
  with no I/O;
* a missing argument local `0` fails, because `get_vars` gives `Error`;
* an entry that returns a location other than `Loc 1 0` fails.

Each follows from HOL's definition by the same reasoning.  HOL `EVAL` cannot
compute `semantics` either.  Bead `flapjack-h29l.9.3`.
-/

namespace Flapjack.Test.WordSemSemanticsParity

open Flapjack Flapjack.WordSemStateFiniteExact

private def s0 : WordSemStateFiniteExact 64 Unit Nat where
  locals := sptFromAList [(0, .loc 1 0)]
  localsSize := some 0
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := []
  stackLimit := 0
  stackMax := some 0
  stackSize := .ln
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  permute := fun _ i => i
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  handler := 0
  clock := 0
  termdep := 2
  code := sptFromAList [(5, (1, WordLangProgHOL.return 0 []))]
  be := false
  ffi := { oracle := fun _ st _ bytes => .ret (st + 1) bytes, ffiState := 0, ioEvents := [] }

theorem evaluate_entry_zero :
    (evaluate (.call none (some 5) [0] none) { s0 with clock := 0 }).1 = some .timeOut := by
  simp (config := { ground := true, decide := true }) only [evaluate]

theorem evaluate_entry_succ (k : Nat) :
    ∃ t, evaluate (.call none (some 5) [0] none) { s0 with clock := k + 1 } =
      (some (.result (.loc 1 0) []), t) ∧ t.ffi.ioEvents = [] := by
  rw [evaluate]
  simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, wordSemBadDestArgs,
    wordSemFindCode, wordSemAddRetLoc, s0, sptFromAList, sptLookup, sptInsert]
  rw [evaluate]
  simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
    WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, sptFromList2, sptLookup,
    flushState, wordSemBadFunReturn]


/-- HOL-level observation: at clock 0 the entry call times out, and at every
    positive clock the entry returns `Result (Loc 1 0) []` with no I/O.  So
    `semantics s0 5 = Terminate Success []`. -/
theorem semantics_return : semantics s0 5 = .terminate .success [] := by
  unfold semantics
  simp only
  split
  · rename_i hc
    obtain ⟨k, hk⟩ := hc
    cases k with
    | zero => rw [evaluate_entry_zero] at hk; exact hk.elim
    | succ k =>
        obtain ⟨t, he, _⟩ := evaluate_entry_succ k
        rw [he] at hk; exact (hk rfl).elim
  · split
    · rename_i res heq
      obtain ⟨k, t, r, outcome, he, hr, rfl⟩ := holOptionSome_some heq
      cases k with
      | zero =>
          have h0 := evaluate_entry_zero; rw [he] at h0; subst h0; exact hr.elim
      | succ k =>
          obtain ⟨t', he', hio⟩ := evaluate_entry_succ k
          rw [he'] at he; cases he
          simp only at hr; rw [hr, hio]
    · rename_i heq
      exfalso
      obtain ⟨t, he, _⟩ := evaluate_entry_succ 0
      exact holOptionSome_none heq _ ⟨1, t, _, .success, he, rfl, rfl⟩

/-- HOL-level observation: without local `0`, `get_vars [0]` fails at every
    clock, which gives `SOME Error` and so `semantics = Fail`. -/
theorem semantics_missing_arg : semantics { s0 with locals := .ln } 5 = .fail := by
  unfold semantics
  simp only
  rw [if_pos]
  refine ⟨0, ?_⟩
  rw [evaluate]
  simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, sptLookup]

/-- HOL-level observation: an entry returning `Loc 2 0` meets the
    `Result ret _` guard with `ret <> Loc 1 0`, so `semantics = Fail`. -/
theorem semantics_bad_return :
    semantics { s0 with locals := sptFromAList [(0, .loc 2 0)] } 5 = .fail := by
  unfold semantics
  simp only
  rw [if_pos]
  refine ⟨1, ?_⟩
  rw [evaluate]
  simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, wordSemBadDestArgs,
    wordSemFindCode, wordSemAddRetLoc, s0, sptFromAList, sptLookup, sptInsert]
  rw [evaluate]
  simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
    WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, sptFromList2, sptLookup,
    flushState, wordSemBadFunReturn]

def runChecks : IO Bool := do
  IO.println "PASS exact wordSem semantics_def observations (Terminate Success [] / Fail / Fail)"
  pure true

end Flapjack.Test.WordSemSemanticsParity
