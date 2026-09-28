import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call

/-!
# `pc_compile_correct` StoreByte case over the exact carriers

The `StoreByte` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:1882-1911`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_StoreByte` (bead `flapjack-pxn.18.4.3.109`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)

/-- HOL `pc_compile_correct[StoreByte]` (`pan_to_crepProofScript.sml:1882-1911`)
    against `pcCompileCorrectAt`. The source `StoreByte destination source`
    evaluates both operands through the tagged exact expression evaluator; the
    only successful path is both `Val (Word _)`, after which HOL's total source
    store `mem_store_byte` updates `memory`. The tagged `compile_exp_val_rel`
    turns the two compiled expression heads into target evaluations to the same
    words, so the tagged target `StoreByte` step performs the same memory update.
    The post-state relations are `state_rel` (memory equality re-established) and
    the unchanged code/exception relations; the result is `none` on both sides.
    No target run is assumed. Untagged: the tagged HOL-shaped statement is
    `pcCompileCorrect_StoreByte`. -/
theorem pcCompileCorrectAt_storeByte {width : Nat} {σ : Type} [NeZero width]
    (destination source : ExpHOL width) (state : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.storeByte destination source : ProgHOL width) state := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocs : localisedExpHOL destination = true ∧ localisedExpHOL source = true := by
    simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_storeByte] at hrun
  cases hdestination : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination with
  | none =>
      simp only [hdestination] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some destinationValue =>
      cases destinationValue with
      | val destinationPayload =>
          cases destinationPayload with
          | word address =>
              cases hsource : @evalHOLExact width σ _ state.toExact
                  (fun address => Classical.propDecidable (state.memaddrs address)) source with
              | none =>
                  simp only [hdestination, hsource] at hrun
                  exact absurd (Prod.mk.inj hrun).1.symm hres
              | some sourceValue =>
                  cases sourceValue with
                  | val sourcePayload =>
                      cases sourcePayload with
                      | word value =>
                          simp only [hdestination, hsource] at hrun
                          cases hstore : @panMemStoreByteWord8HOL width _ state.memory
                              state.memaddrs
                              (fun address => Classical.propDecidable (state.memaddrs address))
                              state.be address (BitVec.ofNat 8 value.toNat) with
                          | none =>
                              simp only [hstore] at hrun
                              exact absurd (Prod.mk.inj hrun).1.symm hres
                          | some memory =>
                              simp only [hstore] at hrun
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
                              rcases hcDst : compileExpExactHOLW ctxt destination with
                                ⟨esDst, shDst⟩
                              obtain ⟨hmapDst, _, _, _⟩ :=
                                @compileExpValRelHOL width σ _ state
                                  (fun address =>
                                    Classical.propDecidable (state.memaddrs address)) ctxt t
                                  (fun address =>
                                    Classical.propDecidable (t.memaddrs address))
                                  destination (.val (.word address)) esDst shDst hdestination
                                  hstate hcode hlocals hlocs.1 hcDst
                              obtain ⟨ceDst, hceDst⟩ : ∃ ce, esDst = [ce] := by
                                rcases esDst with _ | ⟨ce, _ | ⟨_, _⟩⟩
                                · simp [flattenHOL] at hmapDst
                                · exact ⟨ce, rfl⟩
                                · simp [flattenHOL] at hmapDst
                              subst hceDst
                              have hceDstEval : evalCrepSemHOLExp t ceDst = some (.word address) := by
                                simpa [flattenHOL] using hmapDst
                              rcases hcSrc : compileExpExactHOLW ctxt source with
                                ⟨esSrc, shSrc⟩
                              obtain ⟨hmapSrc, _, _, _⟩ :=
                                @compileExpValRelHOL width σ _ state
                                  (fun address =>
                                    Classical.propDecidable (state.memaddrs address)) ctxt t
                                  (fun address =>
                                    Classical.propDecidable (t.memaddrs address))
                                  source (.val (.word value)) esSrc shSrc hsource
                                  hstate hcode hlocals hlocs.2 hcSrc
                              obtain ⟨ceSrc, hceSrc⟩ : ∃ ce, esSrc = [ce] := by
                                rcases esSrc with _ | ⟨ce, _ | ⟨_, _⟩⟩
                                · simp [flattenHOL] at hmapSrc
                                · exact ⟨ce, rfl⟩
                                · simp [flattenHOL] at hmapSrc
                              subst hceSrc
                              have hceSrcEval : evalCrepSemHOLExp t ceSrc = some (.word value) := by
                                simpa [flattenHOL] using hmapSrc
                              have hcomp : compileProgExactHOLW ctxt
                                    (.storeByte destination source : ProgHOL width) =
                                  .storeByte ceDst ceSrc := by
                                simp only [compileProgExactHOLW, compileStoreByteExactHOLW,
                                  hcDst, hcSrc]
                              have hmemT : panMemStoreByteWord8HOL t.memory t.memaddrs t.be
                                    address (BitVec.ofNat 8 value.toNat) = some memory := by
                                rw [← hstate.1, ← hstate.2.1, ← hstate.2.2.2.2.2.2.1]
                                exact hstore
                              have htargetRun : evalCrepSemHOLProgExact t
                                    (compileProgExactHOLW ctxt
                                      (.storeByte destination source : ProgHOL width)) =
                                  (none, { t with memory := memory }) := by
                                simp only [hcomp, evalCrepSemHOLProgExact_storeByte_holShape,
                                  hceDstEval, hceSrcEval, hmemT]
                              refine ⟨none, { t with memory := memory }, htargetRun, ?_, ?_, ?_, ?_⟩
                              · obtain ⟨hmem, haddr, hsh, hstructs, hglob, hclock, hbe, hffi,
                                  hbase, htop⟩ := hstate
                                exact ⟨rfl, haddr, hsh, hstructs, hglob, hclock, hbe, hffi,
                                  hbase, htop⟩
                              · simpa using hcode
                              · simpa using hexcp
                              · exact ⟨rfl, by simpa using hlocals⟩
                  | rStruct _ | nStruct _ _ =>
                      simp only [hdestination, hsource] at hrun
                      exact absurd (Prod.mk.inj hrun).1.symm hres
      | rStruct _ | nStruct _ _ =>
          simp only [hdestination] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres

namespace PcCompileCorrectStoreByteWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged StoreByte case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectStoreByteWitnesses

/-- HOL `pc_compile_correct`, `StoreByte` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:1882`).
    HOL's generated `evaluate_ind` StoreByte conjunct is
    `!dst src s. P (StoreByte dst src,s)`, with no IH (the operands are evaluated
    by `eval`, not recursively). The conclusion is `P (StoreByte dst src, s)`
    unfolded as in `pcCompileCorrectAtHOL`. The translation is the one reviewed
    for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_StoreByte {width : Nat} {σ : Type} [NeZero width] :
    ∀ (destination source : ExpHOL width) (s : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.storeByte destination source : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.storeByte destination source : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.storeByte destination source : ProgHOL width)) =
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
  intro destination source s res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_storeByte destination source s res s1 t ctxt hrun hres hstate hcode
      hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
