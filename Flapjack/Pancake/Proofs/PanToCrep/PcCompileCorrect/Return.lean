import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call

/-!
# `pc_compile_correct` Return case over the exact carriers

The `Return e` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:2056-2071`) in HOL's own shape, from the untagged
`pcCompileCorrectAt_return` (bead `flapjack-pxn.18.4.3.103`).

HOL's proof evaluates the returned expression (`drule compile_exp_val_rel`),
decodes the shape-size check in `compile_def`, and closes both the empty
(`Return []`) and non-empty (`Return ces`) target branches by
`opt_mmap_eq_some`. Both are reproduced below with the tagged
`compile_exp_val_rel` and the tagged `opt_mmap_eq_some`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)

/-- The untagged `Return` case prerequisite against `pcCompileCorrectAt`
    (bead `flapjack-pxn.18.4.3.103`); the tagged HOL-shaped conjunct is
    `pcCompileCorrect_Return` below. -/
theorem pcCompileCorrectAt_return {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (expression : ExpHOL width) :
    pcCompileCorrectAt (.return expression : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocExp : localisedExpHOL expression = true := by
    simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_return] at hrun
  cases hvalue : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) expression with
  | none =>
      rw [hvalue] at hrun
      simp only at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some value =>
      rw [hvalue] at hrun
      simp only at hrun
      by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL source.structs
          (shapeOfHOLExact value) ≤ 32
      · rw [if_pos hsize] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        rcases hc : compileExpExactHOLW ctxt expression with ⟨es, cs⟩
        obtain ⟨hmapEval, _, hshapeval, hwf⟩ :=
          @compileExpValRelHOL width σ _ source
            (fun address => Classical.propDecidable (source.memaddrs address)) ctxt t
            (fun address => Classical.propDecidable (t.memaddrs address))
            expression value es cs
            (by simpa only [PanSemStateFiniteExact.evalHOLFinite] using hvalue) hstate hcode
            hlocals hlocExp hc
        by_cases hsz : sizeOfShapeHOL cs = 0
        · -- `compile_def` emits `Return []` when the decoded shape has size zero.
          have hnil : flattenHOL value = [] := by
            have hlen := flattenHOL_length_eq_sizeOfShapeHOL value (by rw [hshapeval]; exact hwf)
            cases hfl : flattenHOL value with
            | nil => rfl
            | cons head tail => simp [hfl, hshapeval, hsz] at hlen
          refine ⟨some (.return (flattenHOL value)), CrepSemHOLState.emptyLocals t,
            ?_, ?_, ?_, ?_, ?_⟩
          · rw [show compileProgExactHOLW ctxt (.return expression) = .return [] from by
              simp only [compileProgExactHOLW, compileReturnExactHOLW, hc, if_pos hsz]]
            rw [evalCrepSemHOLProgExact_return_holShape]
            simp [hnil]
          · obtain ⟨hmemory, hmemaddrs, hshmemaddrs, hstructs, hglobals, hclock,
              hbe, hffi, hbaseAddr, htopAddr⟩ := hstate
            simp only [panToCrepStateRelFiniteExact]
            exact ⟨hmemory, hmemaddrs, hshmemaddrs, hstructs, hglobals, hclock,
              hbe, hffi, hbaseAddr, htopAddr⟩
          · simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite,
              CrepSemHOLState.emptyLocals] using hcode
          · simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite,
              CrepSemHOLState.emptyLocals] using hexcp
          · rfl
        · -- `compile_def` emits `Return es` otherwise; the compiled expressions
          -- evaluate to `flattenHOL value` by `opt_mmap_eq_some`.
          refine ⟨some (.return (flattenHOL value)), CrepSemHOLState.emptyLocals t,
            ?_, ?_, ?_, ?_, ?_⟩
          · rw [show compileProgExactHOLW ctxt (.return expression) = .return es from by
              simp only [compileProgExactHOLW, compileReturnExactHOLW, hc, if_neg hsz]]
            rw [evalCrepSemHOLProgExact_return_holShape]
            have hmapM : es.mapM (evalCrepSemHOLExp t) = some (flattenHOL value) :=
              (optMmapEqSome es (evalCrepSemHOLExp t) (flattenHOL value)).mpr hmapEval
            rw [hmapM]
          · obtain ⟨hmemory, hmemaddrs, hshmemaddrs, hstructs, hglobals, hclock,
              hbe, hffi, hbaseAddr, htopAddr⟩ := hstate
            simp only [panToCrepStateRelFiniteExact]
            exact ⟨hmemory, hmemaddrs, hshmemaddrs, hstructs, hglobals, hclock,
              hbe, hffi, hbaseAddr, htopAddr⟩
          · simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite,
              CrepSemHOLState.emptyLocals] using hcode
          · simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite,
              CrepSemHOLState.emptyLocals] using hexcp
          · rfl
      · rw [if_neg hsize] at hrun
        exact absurd (Prod.mk.inj hrun).1.symm hres

namespace PcCompileCorrectReturnWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Return case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectReturnWitnesses

/-- HOL `pc_compile_correct`, `Return` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:2056`).
    HOL's printed `evaluate_ind` Return conjunct is `!e s. P (Return e,s)`, with
    no IH. `P` is HOL's induction predicate, unfolded as in `pcCompileCorrectAtHOL`;
    the translation is the one reviewed for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Return {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s : PanSemStateFiniteExact width σ) (expression : ExpHOL width)
      (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.return expression : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.return expression : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.return expression : ProgHOL width)) =
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
  intro s expression res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_return s expression res s1 t ctxt hrun hres hstate hcode hexcp
      hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
