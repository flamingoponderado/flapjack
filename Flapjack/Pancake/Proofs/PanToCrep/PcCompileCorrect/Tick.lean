import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call

/-!
# `pc_compile_correct` Tick case over the exact carriers

The `Tick` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:517-523`): against `pcCompileCorrectAt`, then in HOL's own shape as the tagged
`pcCompileCorrect_Tick` (bead `flapjack-pxn.18.4.3.100`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)

/-- HOL `pc_compile_correct[Tick]` (`pan_to_crepProofScript.sml:517-523`) against
    `pcCompileCorrectAt`. Both clocks agree by `state_rel`. At clock zero both
    sides time out with `empty_locals`; otherwise both decrement the clock and
    keep their locals. No target run is assumed. Untagged: the tagged HOL-shaped
    statement is `pcCompileCorrect_Tick`. -/
theorem pcCompileCorrectAt_tick {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.tick : ProgHOL width) source := by
  intro res s1 t ctxt hrun _ hstate hcode hexcp hlocals _
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_tick] at hrun
  have hclk : source.clock = t.clock := hstate.2.2.2.2.2.1
  simp only [compileProgExactHOLW]
  rw [evalCrepSemHOLProgExact_tick]
  by_cases hc : source.clock = 0
  · rw [if_pos hc] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    rw [if_pos (hclk ▸ hc)]
    exact ⟨_, _, rfl, panToCrepStateRelFiniteExact_emptyLocals source t hstate, hcode, hexcp, rfl⟩
  · rw [if_neg hc] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    rw [if_neg (hclk ▸ hc)]
    refine ⟨_, _, rfl, ?_, hcode, hexcp, rfl, hlocals⟩
    simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.decClockHOLFinite,
      decClockCrepSemHOL, hclk] using hstate

namespace PcCompileCorrectTickWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Tick case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectTickWitnesses

/-- HOL `pc_compile_correct`, `Tick` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:517`).
    HOL's printed `evaluate_ind` Tick conjunct is `!s. P (Tick,s)`, with no IH.
    `P` is HOL's induction predicate, unfolded as in `pcCompileCorrectAtHOL`: the
    conjunctive premise and the inline `case res of`. The translation is the one
    reviewed for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Tick {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s : PanSemStateFiniteExact width σ) (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.tick : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.tick : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.tick : ProgHOL width)) =
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
  intro s res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_tick s res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
