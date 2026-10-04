import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups
import Flapjack.Pancake.Proofs.LoopToWord.ContextSupport

/-!
# `FFI` case of `loop_to_word`'s `compile_correct`

This is the exact `loopSem$evaluate_ind` case of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`) for `FFI`,
resumed at `:1408-1430`.  Bead `flapjack-pxn.18.5.9.26.2`.  The statement
takes the same form as the cases in `CompileCorrect/Base.lean`: HOL's goal
written out for the constructor, with no induction hypothesis.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectFFIWitnesses

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

end LoopToWordCompileCorrectFFIWitnesses

/-- Genuine `FFI` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:1408-1430`).  The
    target reads the four arguments through `find_var` and cuts the locals by
    `mk_new_cutset ctxt cutset`.  `cut_env_mk_new_cutset` gives `locals_rel`
    for the cut, and `cut_env_mk_new_cutset_IMP` keeps register 0.  Both sides
    read the same byte arrays from the equal memory and make the same
    `call_FFI`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_FFI {width : Nat} [NeZero width] {C F : Type}
    (ffiIndex : Flapjack.Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat) (cutset : NumSet) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.ffi ffiIndex ptr1 len1 ptr2 len2 cutset) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.ffi ffiIndex ptr1 len1 ptr2 len2 cutset) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.ffi ffiIndex ptr1 len1 ptr2 len2 cutset) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  have hget : ∀ n w, sptLookup n s.locals = some w →
      WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
    fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState
  split at hEval
  · rename_i w w2 w3 w4 s' h1 h2 h3 h4 hcs
    unfold LoopSemStateFiniteExact.cutState at hcs
    split at hcs
    · rename_i hsub
      cases hcs
      obtain ⟨env, hce, hlr⟩ := LoopToWord.wordSemCutEnvMkNewCutsetHOL ctxt cutset s.locals
        t.locals retv ⟨hLocals, hsub, hRetv⟩
      have h0e := (LoopToWord.wordSemCutEnvMkNewCutsetIMPHOL ctxt cutset t.locals env hce).trans
        hRetv
      simp only [LoopToWord.compHOL]
      rw [WordSemStateFiniteExact.evaluate]
      simp only [hget _ _ h1, hget _ _ h2, hget _ _ h3, hget _ _ h4, hce, hm, hmd, hbe, hffi]
      split at hEval
      · rename_i bytes bytes2 hb1 hb2
        simp only [hb1, hb2]
        split at hEval
        · rename_i o hc
          simp only [Prod.mk.injEq] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          simp only [hc]
          exact ⟨_, _, rfl, by simp [WordSemStateFiniteExact.flushState,
            LoopSemStateFiniteExact.callEnv, hffi], rfl⟩
        · rename_i nf nb hc
          simp only [Prod.mk.injEq] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          simp only [hc]
          refine ⟨_, _, rfl, rfl, ⟨len, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩, rfl, h0e, hlr,
            rfl, rfl⟩ <;> first | rfl | assumption
      · simp only [Prod.mk.injEq] at hEval
        exact absurd hEval.1.symm hNE
    · cases hcs
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

end Flapjack
