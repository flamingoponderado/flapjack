import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups

/-!
# `Return` and `Raise` cases of `loop_to_word`'s `compile_correct`

These are the exact `loopSem$evaluate_ind` cases of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`) for `Return` and
`Raise`, resumed at `:736-760`.  Bead `flapjack-pxn.18.5.9.24`.  The
statements take the same form as the base cases in `CompileCorrect/Base.lean`:
HOL's goal written out for the constructor, with no induction hypothesis.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectReturnRaiseWitnesses

/-- Same-module roundtrip for the relation qualifier's loopSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the relation qualifier's wordSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordCompileCorrectReturnRaiseWitnesses

/-- Flapjack helper (no HOL declaration).  A successful `jump_exc` changes
    only `handler`, `locals`, `stack` and `locals_size`.  Restoring the
    original `stack` and `handler` of the result gives the same jump again.
    This is the fact HOL's `Raise` case uses after unfolding `jump_exc_def`. -/
theorem wordSemJumpExc_some_restore {width : Nat} [NeZero width] {C F : Type}
    (t t' : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (h : WordSemStateFiniteExact.jumpExc t = some (t', l1, l2)) :
    (∃ n loc xs m, t' = { t with handler := n, locals := loc, stack := xs, localsSize := m }) ∧
      WordSemStateFiniteExact.jumpExc { t' with stack := t.stack, handler := t.handler } =
        some (t', l1, l2) := by
  unfold WordSemStateFiniteExact.jumpExc at h
  split at h
  · rename_i hlt
    split at h
    · rename_i m e0 e n k1 k2 xs hl
      cases h
      refine ⟨⟨_, _, _, _, rfl⟩, ?_⟩
      unfold WordSemStateFiniteExact.jumpExc
      simp only [hlt, if_true, hl]
    · cases h
  · cases h

/-- Genuine `Return` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:736-745`).  There is no
    induction hypothesis.  The compiled `Return 0 (MAP (find_var ctxt) ns)`
    reads `retv` from register 0; `~isWord retv` makes it a `Loc`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Return {width : Nat} [NeZero width] {C F : Type}
    (ns : List Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.return ns) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.return ns) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.return ns) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, -, hWord, -⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · rename_i vs hvs
    simp only [Prod.mk.injEq] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    obtain ⟨hgv, -⟩ := LoopToWord.localsRelHOLGetVars ctxt s t ns vs ⟨hLocals, hvs⟩
    obtain ⟨len, hmem, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState
    cases retv with
    | word w => simp [wordSemIsWordLoc] at hWord
    | loc l1 l2 =>
      refine ⟨WordSemStateFiniteExact.flushState false t, some (.result (.loc l1 l2) vs), ?_, ?_, ?_⟩
      · simp only [LoopToWord.compHOL]
        rw [WordSemStateFiniteExact.evaluate]
        simp [WordSemStateFiniteExact.getVar, hRetv, hgv]
      · simp [WordSemStateFiniteExact.flushState, LoopSemStateFiniteExact.callEnv, hffi]
      · refine ⟨⟨len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩ <;>
          simp_all [WordSemStateFiniteExact.flushState, LoopSemStateFiniteExact.callEnv]
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

/-- Genuine `Raise` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:747-760`).  There is no
    induction hypothesis.  When the target `jump_exc` fails, the target
    result is `Error`, which the `Exception` arm of HOL's goal allows. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Raise {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.raise n) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.raise n) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.raise n) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, -, -, -, -⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE
  · rename_i w hw
    simp only [Prod.mk.injEq] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    have hgv := LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, hw⟩
    obtain ⟨len, hmem, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState
    cases hj : WordSemStateFiniteExact.jumpExc t with
    | none =>
      refine ⟨t, some .error, ?_, ?_, ?_, fun h => absurd rfl h, ?_⟩
      · simp only [LoopToWord.compHOL]
        rw [WordSemStateFiniteExact.evaluate]
        simp [hgv, hj]
      · simpa [LoopSemStateFiniteExact.callEnv] using hffi
      · refine ⟨len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp_all [LoopSemStateFiniteExact.callEnv]
      · intro r m1 m2 h
        have ht : ({ t with stack := t.stack, handler := t.handler } :
            WordSemStateFiniteExact width C F) = t := rfl
        rw [ht, hj] at h
        cases h
    | some p =>
      obtain ⟨t', l1, l2⟩ := p
      obtain ⟨⟨hn, loc, xs, m, rfl⟩, hre⟩ := wordSemJumpExc_some_restore t _ l1 l2 hj
      refine ⟨{ t with handler := hn, locals := loc, stack := xs, localsSize := m },
        some (.exception (.loc l1 l2) w), ?_, ?_, ?_, fun _ => ⟨_, _, rfl⟩, ?_⟩
      · simp only [LoopToWord.compHOL]
        rw [WordSemStateFiniteExact.evaluate]
        simp [hgv, hj]
      · simpa [LoopSemStateFiniteExact.callEnv] using hffi
      · refine ⟨len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp_all [LoopSemStateFiniteExact.callEnv]
      · intro r m1 m2 h
        rw [hre] at h
        cases h
        exact ⟨rfl, rfl⟩

end Flapjack
