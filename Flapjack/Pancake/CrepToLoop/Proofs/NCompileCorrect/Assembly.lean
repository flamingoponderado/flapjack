import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Leaf
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Seq
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Primitive
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Store
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Dec
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.While
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Call
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.ShMem
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd

/-!
# crep_to_loop `ncompile_correct`: assembly of the `evaluate_ind` cases

HOL proves `ncompile_correct` (`crep_to_loopProofScript.sml:110-154`) by
`recInduct crepSemTheory.evaluate_ind` and resumes each case.  This module applies
the tagged Lean port `evalCrepSemHOLProgExact_induct` (`evaluate_ind`) to the case
pieces, all stated over the canonical `NCompileCorrect.PropertyAt`.
-/

namespace Flapjack

open Pancake.CrepToLoop.Proofs.NCompileCorrect

private theorem lookupCodeFinite_eq_HOLFinite' {width : Nat} [NeZero width]
    (c : HolFiniteMapExact Flapjack.Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width))
    (f : Flapjack.Basis.Pure.MlString.MlString) (args : List (HolWordLab width)) (len : Nat) :
    lookupCodeFiniteHOL c f args len = lookupCodeHOLFinite c.lookup f args len := by
  have h1 := lookupCodeFiniteHOL_lookup c f args len
  unfold lookupCodeHOLFinite
  split
  · rename_i hn
    rw [hn] at h1
    cases hF : lookupCodeFiniteHOL c f args len with
    | none => rfl
    | some val => rw [hF] at h1; simp at h1
  · rename_i body cl hs
    rw [hs] at h1
    cases hF : lookupCodeFiniteHOL c f args len with
    | none => rw [hF] at h1; simp at h1
    | some val =>
        obtain ⟨b, m⟩ := val
        rw [hF] at h1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, hm⟩ := h1
        congr 2
        exact holFiniteMapExact_eq_of_lookup_eq hm

/-- Flapjack helper (no HOL declaration): HOL `ncompile_correct`'s
    `recInduct crepSemTheory.evaluate_ind` assembly of all the case pieces, given
    the `Store32` and `StoreByte` cases (beads `flapjack-pxn.18.5.6.52`/`.53`) in
    `PropertyAt` form.  The tagged assembled theorem instantiates these two. -/
theorem crepToLoopNcompileCorrectOf {width : Nat} [NeZero width] {σ : Type}
    (hstore32 : ∀ (dst src : CrepExpHOL width) (s : CrepSemHOLState width σ),
      PropertyAt (.store32 dst src) s)
    (hstoreByte : ∀ (dst src : CrepExpHOL width) (s : CrepSemHOLState width σ),
      PropertyAt (.storeByte dst src) s) :
    ∀ (v : CrepProgHOL width) (s : CrepSemHOLState width σ), PropertyAt v s := by
  intro v s
  apply evalCrepSemHOLProgExact_induct (P := fun x => PropertyAt x.1 x.2)
  all_goals try simp only [crepExactEvalExpClassical_eq] at *
  · intro s res s1 t ctxt l
    exact ncompileCorrectSkipCase s res s1 t ctxt l
  · intro v e prog s ih res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_dec v e prog s ih res s1 t ctxt l
      ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro lhss pop rhss s res s1 t ctxt l
    exact crepToLoop_ncompile_correct_primitive lhss pop rhss s res s1 t ctxt l
  · intro v src s res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_assign v src s res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro dst src s res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_store dst src s res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · exact hstore32
  · exact hstoreByte
  · intro dst src s res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_storeGlob dst src s res s1 t ctxt l
      ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro op v ad s res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_shMem op v ad s res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro c1 c2 s ih2 ih1 res s1 t ctxt l
    exact crepToLoop_ncompile_correct_seq ctxt l c1 c2 s ih2 ih1 t res s1
  · intro e c1 c2 s ih res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_if e c1 c2 s (fun w hw => ih _ w hw rfl) res s1 t ctxt l
      ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro n s res s1 t ctxt l
    exact ncompileCorrectBreakCase n s res s1 t ctxt l
  · intro n s res s1 t ctxt l
    exact ncompileCorrectContinueCase n s res s1 t ctxt l
  · intro e c s ih1 ih2 ih3 res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_while e c s
      (fun w r s1' ⟨h1, h2, h3, h4, h5⟩ => ih1 _ w r s1' _ 0 h1 rfl h2 h3 h4.symm h5 rfl rfl)
      (fun w r s1' ⟨h1, h2, h3, h4, h5⟩ => ih2 _ w r s1' h1 rfl h2 h3 h4.symm h5)
      (fun w ⟨h1, h2, h3⟩ => ih3 _ w h1 rfl h2 h3)
      res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro es s res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_return es s res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro eid s res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_raise eid s res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro s res s1 t ctxt l
    exact ncompileCorrectTickCase s res s1 t ctxt l
  · intro caltyp fname argexps s ihh ihb res s1 t ctxt l he hne hs hm hg hc hl
    have hfun : crepExactEvalExpClassical s = evalCrepSemHOLExp s :=
      funext (crepExactEvalExpClassical_eq s)
    exact crepToLoop_ncompile_correct_call caltyp fname argexps s
      (fun args prog newlocals st eid rts p ⟨h1, h2, h3, h4, h5, h6⟩ =>
        ihh args (prog, newlocals) prog newlocals _ _ st _ eid _ _ _ _ eid p
          (by rw [hfun]; exact h1) (by rw [← lookupCodeFinite_eq_HOLFinite']; exact h2) rfl
          (by subst h6; simpa using h3) h4 h5.symm rfl rfl rfl h6 rfl rfl rfl rfl)
      (fun args prog newlocals ⟨h1, h2, h3, h4⟩ =>
        ihb args (prog, newlocals) prog newlocals (by rw [hfun]; exact h1)
          (by rw [← lookupCodeFinite_eq_HOLFinite']; exact h2) rfl
          (by cases caltyp with
              | none => simp
              | some x => obtain ⟨rts, y⟩ := x; simpa using h3) h4)
      res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro f p1 l1 p2 l2 s res s1 t ctxt l he hne hs hm hg hc hl
    exact crepToLoop_ncompile_correct_extCall f p1 l1 p2 l2 s res s1 t ctxt l
      ⟨he, hne, hs, hm, hg, hc, hl⟩

end Flapjack
