import Flapjack.Compiler.Backend.Semantics.StackSem.LocValueCase
open Flapjack Flapjack.StackSem Flapjack.StackSemLocValueCase
open Flapjack.Compiler.Backend.StackLang

/- Kernel replay of scripts/hol-probes/stacksem_loc_value_probe.out. The
existential label alternative is proved from the actual stored program. -/
private abbrev leaf : HolProg 8 := .locValue 1 4 5
private abbrev ret : HolProg 8 := .call (some (leaf, 13, 4, 5)) (.inl 0) none
private abbrev handler : HolProg 8 :=
  .call (some (leaf, 13, 11, 12)) (.inl 0) (some (leaf, 14, 15))
private abbrev noRet : HolProg 8 := .call none (.inl 0) (some (leaf, 14, 15))
private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F)
    (code : Spt (HolProg 8)) (useStack : Bool) :=
  { s with
    code := code
    useStack := useStack
    stack := [.word 11, .loc 3 4]
    stackSpace := 1
    regs := HolFiniteMapExact.empty.updateEq (7, .word 9)
    clock := 17
    memory := fun _ => .word 23 }
private def observe {C F : Type}
    (result : Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) :=
  (result.1, result.2.regs.lookup 7, result.2.stack, result.2.stackSpace,
    result.2.clock, result.2.memory 0)

private theorem present : locCheckExact (sptInsert 3 ret .ln) (4, 5) := by
  exact Or.inr ⟨3, ret, sptLookup_sptInsert_same 3 ret .ln,
    by simp [getLabelsExact, ret, leaf]⟩
private theorem handlerPresent : locCheckExact (sptInsert 3 handler .ln) (14, 15) := by
  exact Or.inr ⟨3, handler, sptLookup_sptInsert_same 3 handler .ln,
    by simp [getLabelsExact, handler, leaf]⟩
private theorem noRetAbsent : ¬ locCheckExact (sptInsert 3 noRet .ln) (14, 15) := by
  rintro (⟨hz, _⟩ | ⟨key, program, hl, hp⟩)
  · omega
  · by_cases hk : key = 3
    · subst key
      rw [sptLookup_sptInsert_same] at hl
      cases hl
      simp [getLabelsExact, noRet] at hp
    · rw [sptLookup_sptInsert_ne 3 key noRet .ln hk] at hl
      simp [sptLookup] at hl

variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)

-- loc_zero_present
example : observe (locValue 7 3 0 (fixture s (sptInsert 3 ret .ln) true)) =
    (none, some (.loc 3 0), [.word 11, .loc 3 4], 1, 17, .word 23) := by
  have h : locCheckExact (fixture s (sptInsert 3 ret .ln) true).code (3, 0) :=
    Or.inl ⟨rfl, by simp [fixture, sptMem, sptDomain, sptLookup_sptInsert_same]⟩
  rw [locValue_success 7 3 0 _ h]
  cbv

-- loc_zero_absent
example : observe (locValue 7 3 0 (fixture s .ln true)) =
    (some .error, some (.word 9), [.word 11, .loc 3 4], 1, 17, .word 23) := by
  have h : ¬ locCheckExact (fixture s .ln true).code (3, 0) := by
    simp [fixture, locCheckExact, sptMem, sptDomain]
  rw [locValue_failure 7 3 0 _ h]
  cbv

-- loc_nonzero_present
example : observe (locValue 7 4 5 (fixture s (sptInsert 3 ret .ln) true)) =
    (none, some (.loc 4 5), [.word 11, .loc 3 4], 1, 17, .word 23) := by
  rw [locValue_success 7 4 5 _ present]
  cbv

-- loc_handler_present
example : observe (locValue 7 14 15 (fixture s (sptInsert 3 handler .ln) true)) =
    (none, some (.loc 14 15), [.word 11, .loc 3 4], 1, 17, .word 23) := by
  rw [locValue_success 7 14 15 _ handlerPresent]
  cbv

-- loc_handler_no_return
example : observe (locValue 7 14 15 (fixture s (sptInsert 3 noRet .ln) true)) =
    (some .error, some (.word 9), [.word 11, .loc 3 4], 1, 17, .word 23) := by
  rw [locValue_failure 7 14 15 _ noRetAbsent]
  cbv

-- loc_disabled_stack: LocValue has no use_stack gate.
example : observe (locValue 7 4 5 (fixture s (sptInsert 3 ret .ln) false)) =
    (none, some (.loc 4 5), [.word 11, .loc 3 4], 1, 17, .word 23) := by
  rw [locValue_success 7 4 5 _ present]
  cbv
