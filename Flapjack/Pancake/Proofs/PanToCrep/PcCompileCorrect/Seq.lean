import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call

/-!
# `pc_compile_correct` Seq case over the exact carriers

The `Seq c1 c2` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:2143-2164`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_Seq` (bead `flapjack-pxn.18.4.3.96`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)

/-- HOL `pc_compile_correct[Seq]` (`pan_to_crepProofScript.sml:2143-2164`) against
    `pcCompileCorrectAt`, from the two Seq IHs of the rebound `evaluate_ind`:
    `P (c2, s1)` after `c1` completes normally in `s1`, and `P (c1, s)`. When
    `c1` completes normally, both targets continue with `compile ctxt c2`.
    Otherwise both sides stop with `c1`'s result, which is not `NONE` in the
    target either. No target run is assumed. Untagged: the tagged HOL-shaped
    statement is `pcCompileCorrect_Seq`. -/
theorem pcCompileCorrectAt_seq {width : Nat} {σ : Type} [NeZero width]
    (c1 c2 : ProgHOL width) (source : PanSemStateFiniteExact width σ)
    (ih2 : ∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
      source.evaluateHOLFiniteState c1 = (res, s1) → res = none → pcCompileCorrectAt c2 s1)
    (ih1 : pcCompileCorrectAt c1 source) :
    pcCompileCorrectAt (.seq c1 c2 : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocs : localisedProgHOL c1 = true ∧ localisedProgHOL c2 = true := by
    simpa [localisedProgHOL] using hloc
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  rcases h1 : source.evaluateHOLFiniteState c1 with ⟨r1, s'⟩
  rw [h1] at hrun
  dsimp only at hrun
  simp only [compileProgExactHOLW]
  rw [evalCrepSemHOLProgExact_seq_holShape]
  rcases r1 with _ | r1
  · obtain ⟨res1, t1, hrun1, hs, hc, he, hrr⟩ :=
      ih1 none s' t ctxt h1 (by simp) hstate hcode hexcp hlocals hlocs.1
    obtain ⟨rfl, hl⟩ := hrr
    rw [hrun1]
    dsimp only
    rw [if_pos rfl]
    exact ih2 none s' h1 rfl res s1 t1 ctxt hrun hres hs hc he hl hlocs.2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨res1, t1, hrun1, hs, hc, he, hrr⟩ :=
      ih1 (some r1) s' t ctxt h1 hres hstate hcode hexcp hlocals hlocs.1
    have hne : res1 ≠ none := by
      intro hn
      subst hn
      cases r1 with
      | exception eid v =>
          simp only [pcCompileCorrectResultRel] at hrr
          split at hrr
          · exact hrr
          · exact absurd hrr.1 (by simp)
      | _ => simp [pcCompileCorrectResultRel] at hrr
    rw [hrun1]
    dsimp only
    rw [if_neg hne]
    exact ⟨res1, t1, rfl, hs, hc, he, hrr⟩

namespace PcCompileCorrectSeqWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Seq case below (delegating to the imported checked witnesses). -/

theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact

theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_CrepSemHOLState state

end PcCompileCorrectSeqWitnesses

/-- HOL `pc_compile_correct`, `Seq` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:2143`).
    HOL's printed `evaluate_ind` Seq conjunct is
    `!c1 c2 s. (!res s1. (res,s1) = evaluate (c1,s) /\ res = NONE ==> P (c2,s1)) /\
      P (c1,s) ==> P (Seq c1 c2,s)`; the IHs are transcribed in that order and
    orientation, at `P = pcCompileCorrectAtHOL`. The conclusion is
    `P (Seq c1 c2, s)` unfolded as in `pcCompileCorrectAtHOL`. The translation is
    the one reviewed for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Seq {width : Nat} {σ : Type} [NeZero width] :
    ∀ (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      (∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
          (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s c1 ∧ res = none →
          pcCompileCorrectAtHOL c2 s1) ∧
        pcCompileCorrectAtHOL c1 s →
      ∀ (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.seq c1 c2 : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.seq c1 c2 : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.seq c1 c2 : ProgHOL width)) =
          (res1, t1) ∧
        panToCrepStateRelFiniteExact s1 t1 ∧ codeRelExactHOLW ctxt s1.code t1.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
        match res with
        | none => res1 = none ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some .error => False
        | some .timeOut => res1 = some .timeOut
        | some .break =>
            res1 = some (.break 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some .continue =>
            res1 = some (.continue 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some (.returned rv) => res1 = some (.return (flattenHOL rv))
        | some (.exception eid v') =>
            (match ctxt.eids.lookup eid with
             | none => False
             | some n =>
                 res1 = some (.exception n) ∧
                 (1 ≤ sizeOfShapeHOL (shapeOfHOLExact v') →
                   globalsLookupHOL t1 v' = some (flattenHOL v') ∧
                     sizeOfShapeHOL (shapeOfHOLExact v') ≤ 32))
        | some (.finalFfi f) => res1 = some (.finalFfi f) := by
  intro c1 c2 s ⟨ihSecond, ihFirst⟩ res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_seq c1 c2 s
      (fun r s' hr hn => (pcCompileCorrectAt_iff_HOL _ _).mpr (ihSecond r s' ⟨hr.symm, hn⟩))
      ((pcCompileCorrectAt_iff_HOL _ _).mpr ihFirst)
      res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
