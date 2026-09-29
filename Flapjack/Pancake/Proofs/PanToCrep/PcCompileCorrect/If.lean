import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call

/-!
# `pc_compile_correct` If case over the exact carriers

The `If e c1 c2` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:2166-2186`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_If` (bead `flapjack-pxn.18.4.3.98`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)

/-- HOL `pc_compile_correct[If]` (`pan_to_crepProofScript.sml:2166-2186`) against
    `pcCompileCorrectAt`, from the If IH of the rebound `evaluate_ind`: `P` at the
    selected branch after the condition evaluates to `Val (Word w)`. By the tagged
    `compile_exp_val_rel`, the compiled condition is a single expression that
    evaluates to `Word w` in the target, so both sides select the same branch.
    Any other condition value is a source Error, excluded by `res ≠ SOME Error`.
    No target run is assumed. Untagged: the tagged HOL-shaped statement is
    `pcCompileCorrect_If`. -/
theorem pcCompileCorrectAt_ite {width : Nat} {σ : Type} [NeZero width]
    (e : ExpHOL width) (c1 c2 : ProgHOL width) (source : PanSemStateFiniteExact width σ)
    (ih : ∀ w : BitVec width,
      @evalHOLExact width σ _ source.toExact
          (fun address => Classical.propDecidable (source.memaddrs address)) e =
        some (.val (.word w)) →
      pcCompileCorrectAt (if w ≠ 0 then c1 else c2) source) :
    pcCompileCorrectAt (.ite e c1 c2 : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocs : localisedExpHOL e = true ∧ localisedProgHOL c1 = true ∧
      localisedProgHOL c2 = true := by
    simpa [localisedProgHOL, Bool.and_assoc] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_ite] at hrun
  split at hrun
  case h_2 =>
    exact absurd (Prod.mk.inj hrun).1.symm hres
  rename_i w heval
  rcases hc : compileExpExactHOLW ctxt e with ⟨es, sh⟩
  obtain ⟨hes, _, _, _⟩ :=
    @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) ctxt t
      (fun address => Classical.propDecidable (t.memaddrs address))
      e (.val (.word w)) es sh heval hstate hcode hlocals hlocs.1 hc
  obtain ⟨ce, hce⟩ : ∃ ce, es = [ce] := by
    rcases es with _ | ⟨ce, _ | ⟨_, _⟩⟩
    · simp [flattenHOL] at hes
    · exact ⟨ce, rfl⟩
    · simp [flattenHOL] at hes
  subst hce
  have hce : @evalCrepSemHOLExp width _ σ t ce = some (.word w) := by
    simpa [flattenHOL] using hes
  have hcomp : compileProgExactHOLW ctxt (.ite e c1 c2) =
      .ite ce (compileProgExactHOLW ctxt c1) (compileProgExactHOLW ctxt c2) := by
    simp only [compileProgExactHOLW, compileIfExactHOLW, hc]
  rw [hcomp, evalCrepSemHOLProgExact_ite_holShape, hce]
  dsimp only
  have hih := ih w heval
  by_cases hw : w = 0
  · rw [if_pos hw] at hrun
    have hne : ¬ (w ≠ 0) := fun h => h hw
    rw [if_neg hne] at hih ⊢
    exact hih res s1 t ctxt hrun hres hstate hcode hexcp hlocals hlocs.2.2
  · rw [if_neg hw] at hrun
    rw [if_pos hw] at hih ⊢
    exact hih res s1 t ctxt hrun hres hstate hcode hexcp hlocals hlocs.2.1

namespace PcCompileCorrectIfWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged If case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectIfWitnesses

/-- HOL `pc_compile_correct`, `If` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:2166`).
    HOL's printed `evaluate_ind` If conjunct is
    `!e c1 c2 s. (!v1 v6 w. eval s e = SOME v1 /\ v1 = Val v6 /\ v6 = Word w ==>
      P (if w <> 0w then c1 else c2,s)) ==> P (If e c1 c2,s)`; the IH is
    transcribed binder for binder, at `P = pcCompileCorrectAtHOL`. `eval s` is the
    tagged exact expression evaluator with the classical address decision, as in
    the tagged Pan If arm (`evaluateHOLFiniteState_ite`). The conclusion is
    `P (If e c1 c2, s)` unfolded as in `pcCompileCorrectAtHOL`. The translation is
    the one reviewed for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_If {width : Nat} {σ : Type} [NeZero width] :
    ∀ (e : ExpHOL width) (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      (∀ (v1 : ValueHOL width) (v6 : HolWordLab width) (w : BitVec width),
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v1 ∧
            v1 = .val v6 ∧ v6 = .word w →
          pcCompileCorrectAtHOL (if w ≠ 0 then c1 else c2) s) →
      ∀ (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.ite e c1 c2 : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.ite e c1 c2 : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.ite e c1 c2 : ProgHOL width)) =
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
  intro e c1 c2 s ih res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_ite e c1 c2 s
      (fun w hw => (pcCompileCorrectAt_iff_HOL _ _).mpr (ih _ _ w ⟨hw, rfl, rfl⟩))
      res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
