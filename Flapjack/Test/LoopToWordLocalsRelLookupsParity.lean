import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups

/-!
Direct comparison rows for HOL `locals_rel_get_var`/`locals_rel_get_vars`
from `scripts/hol-probes/loop_to_word_locals_rel_probe.out`.  The positive
fixture maps source locals 1,2 to target word locals 4,6.  Miss rows preserve
the evaluator's fail-on-first-missing-lookup behavior.
-/

namespace Flapjack.Test.LoopToWordLocalsRelLookupsParity

open Flapjack Flapjack.LoopToWord

private def context : Spt Nat := sptInsert 2 6 (sptInsert 1 4 .ln)
private def sourceLocals : Spt (WordLocW 64) :=
  sptInsert 2 (.word 9) (sptInsert 1 (.word 7) .ln)
private def targetLocals : Spt (WordLocW 64) :=
  sptInsert 6 (.word 9) (sptInsert 4 (.word 7) .ln)

private theorem contextMem (name : Nat) :
    sptMem name context ↔ name = 1 ∨ name = 2 := by
  rw [sptMem_iff_lookup]
  constructor
  · rintro ⟨value, hlookup⟩
    by_cases h1 : name = 1
    · exact Or.inl h1
    · by_cases h2 : name = 2
      · exact Or.inr h2
      · rw [context, sptLookup_sptInsert_ne 2 name 6 (sptInsert 1 4 .ln) h2,
          sptLookup_sptInsert_ne 1 name 4 .ln h1, sptLookup] at hlookup
        simp at hlookup
  · rintro (rfl | rfl)
    · exact ⟨4, by rw [context, sptLookup_sptInsert_ne 2 1 6 (sptInsert 1 4 .ln) (by decide),
        sptLookup_sptInsert_same]⟩
    · exact ⟨6, by rw [context, sptLookup_sptInsert_same]⟩

private theorem contextEven (name register : Nat)
    (hlookup : sptLookup name context = some register) :
    register ≠ 0 ∧ register % 2 = 0 := by
  by_cases h1 : name = 1
  · subst name
    rw [context, sptLookup_sptInsert_ne 2 1 6 (sptInsert 1 4 .ln) (by decide),
      sptLookup_sptInsert_same] at hlookup
    injection hlookup with hreg
    subst register
    decide
  · by_cases h2 : name = 2
    · subst name
      rw [context, sptLookup_sptInsert_same] at hlookup
      injection hlookup with hreg
      subst register
      decide
    · rw [context, sptLookup_sptInsert_ne 2 name 6 (sptInsert 1 4 .ln) h2,
        sptLookup_sptInsert_ne 1 name 4 .ln h1, sptLookup] at hlookup
      simp at hlookup

private theorem contextSimulation (name : Nat) (value : WordLocW 64)
    (hsource : sptLookup name sourceLocals = some value) :
    ∃ register, sptLookup name context = some register ∧
      sptLookup register targetLocals = some value := by
  by_cases h1 : name = 1
  · subst name
    have hvalue : value = WordLocW.word 7 := by
      simpa [sourceLocals, sptLookup, sptInsert] using hsource.symm
    subst value
    refine ⟨4, ?_, ?_⟩ <;> simp [context, targetLocals, sptLookup, sptInsert]
  · by_cases h2 : name = 2
    · subst name
      have hvalue : value = WordLocW.word 9 := by
        simpa [sourceLocals, sptLookup, sptInsert] using hsource.symm
      subst value
      refine ⟨6, ?_, ?_⟩ <;> simp [context, targetLocals, sptLookup, sptInsert]
    · simp [sourceLocals, sptLookup, sptInsert] at hsource
      split at hsource <;> simp_all <;> omega

private theorem fixtureRel : localsRelHOL (width := 64) context sourceLocals targetLocals := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right hleft hright heq
    have hleft' := (contextMem left).mp hleft
    have hright' := (contextMem right).mp hright
    rcases hleft' with rfl | rfl <;> rcases hright' with rfl | rfl
    · rfl
    · simp [findVarHOL, context, sptLookup, sptInsert] at heq
    · simp [findVarHOL, context, sptLookup, sptInsert] at heq
    · rfl
  · exact contextEven
  · exact contextSimulation

private def exactFfi : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state []
    ffiState := ()
    ioEvents := [] }

private def sourceState : LoopSemStateFiniteExact 64 Unit where
  locals := sourceLocals
  globals := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  clock := 0
  code := .ln
  be := false
  ffi := exactFfi
  baseAddr := 0
  topAddr := 0

private def targetState : WordSemStateFiniteExact 64 Unit Unit where
  locals := targetLocals
  localsSize := none
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := []
  stackLimit := 0
  stackMax := none
  stackSize := .ln
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  permute := fun _ _ => 0
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  handler := 0
  clock := 0
  termdep := 0
  code := .ln
  be := false
  ffi := exactFfi

example : LoopSemStateFiniteExact.getVars [1, 2] sourceState = some [.word 7, .word 9] := by
  simp [sourceState, LoopSemStateFiniteExact.getVars, sourceLocals,
    sptLookup, sptInsert]

example : LoopSemStateFiniteExact.getVars [1, 3] sourceState = none := by
  simp [sourceState, LoopSemStateFiniteExact.getVars, sourceLocals,
    sptLookup, sptInsert]

example : WordSemStateFiniteExact.getVars [4, 6] targetState = some [.word 7, .word 9] := by
  simp [targetState, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
    targetLocals, sptLookup, sptInsert]

example : WordSemStateFiniteExact.getVars [4, 5] targetState = none := by
  simp [targetState, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
    targetLocals, sptLookup, sptInsert]

example : WordSemStateFiniteExact.getVar (findVarHOL context 1) targetState = some (.word 7) := by
  exact localsRelHOLGetVar context sourceLocals targetState 1 (.word 7)
    ⟨fixtureRel, by simp [sourceLocals, sptLookup, sptInsert]⟩

example :
    WordSemStateFiniteExact.getVars ([1, 2].map (findVarHOL context)) targetState =
      some [.word 7, .word 9] ∧ [WordLocW.word (7 : BitVec 64), .word 9].length = [1, 2].length := by
  exact localsRelHOLGetVars context sourceState targetState [1, 2] [.word 7, .word 9]
    ⟨fixtureRel, by simp [sourceState, LoopSemStateFiniteExact.getVars,
      sourceLocals, sptLookup, sptInsert]⟩

def parityRows : Bool :=
  LoopSemStateFiniteExact.getVars [1, 2] sourceState == some [.word 7, .word 9] &&
  LoopSemStateFiniteExact.getVars [1, 3] sourceState == none &&
  WordSemStateFiniteExact.getVars [4, 6] targetState == some [.word 7, .word 9] &&
  WordSemStateFiniteExact.getVars [4, 5] targetState == none

#guard parityRows

def runChecks : IO Bool := do
  if parityRows then
    IO.println "PASS Loop-to-Word locals_rel_get_var/get_vars exact oracle rows"
  else
    IO.println "FAIL Loop-to-Word locals_rel_get_var/get_vars exact oracle rows"
  pure parityRows

end Flapjack.Test.LoopToWordLocalsRelLookupsParity
