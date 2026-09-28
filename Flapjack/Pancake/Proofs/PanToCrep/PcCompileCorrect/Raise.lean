import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.DecCall

/-!
# `pc_compile_correct` Raise case over the exact carriers

The `Raise eid e` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:2071-2141`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_Raise` (bead `flapjack-pxn.18.4.3.104`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL StructContextExact
  isWfShapeExactHOL)

/-- The global addresses `GENLIST (λx. n2w x) n : word5 list` are distinct when
    `n ≤ 32`. -/
private theorem globalAddrs_nodup (n : Nat) (hn : n ≤ 32) :
    ((List.range n).map (fun x => BitVec.ofNat 5 x)).Nodup := by
  apply List.pairwise_map.mpr
  apply List.nodup_range.imp_of_mem
  intro a b ha hb hab heq
  simp only [List.mem_range] at ha hb
  have := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- HOL `pc_compile_correct[Raise]` (`pan_to_crepProofScript.sml:2071-2141`)
    against `pcCompileCorrectAt`. The source raises `Exception eid value` with
    `empty_locals` after the shape and size checks; `excp_rel` gives the target
    code `n` for `eid`. By the tagged `compile_exp_val_rel`, the compiled
    expressions evaluate to `flatten value`. The fresh temporaries hold them
    (`eval_nested_decs_seq_res_var_eq`), `store_globals` writes them to globals
    `0w ..` (`evaluate_seq_store_globals_res`), the temporaries are restored
    (`res_var_lookup_original_eq`), and `Raise n` fires, so `globals_lookup`
    reads back `flatten value`. Every other outcome is a source Error, excluded by
    `res ≠ SOME Error`. No target run is assumed. Untagged: the tagged
    HOL-shaped statement is `pcCompileCorrect_Raise`. -/
theorem pcCompileCorrectAt_raise {width : Nat} {σ : Type} [NeZero width]
    (eid : MlS) (e : ExpHOL width) (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.raise eid e : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hloce : localisedExpHOL e = true := by simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_raise] at hrun
  cases hes : source.eshapes.lookup eid with
  | none =>
      rw [hes] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some shape =>
  cases heval : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) e with
  | none =>
      rw [hes, heval] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some value =>
  rw [hes, heval] at hrun
  dsimp only at hrun
  split at hrun
  case isFalse => exact absurd (Prod.mk.inj hrun).1.symm hres
  rename_i hcond
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  obtain ⟨n, hn⟩ : ∃ n, ctxt.eids.lookup eid = some n := by
    have := hexcp.1 eid
    rw [hes] at this
    exact Option.isSome_iff_exists.mp this.symm
  rcases hc : compileExpExactHOLW ctxt e with ⟨es, sh⟩
  obtain ⟨hev, hlen, hsh, hwf⟩ :=
    @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) ctxt t
      (fun address => Classical.propDecidable (t.memaddrs address))
      e value es sh heval hstate hcode hlocals hloce hc
  subst hsh
  have hflen : (flattenHOL value).length = sizeOfShapeHOL (shapeOfHOLExact value) :=
    flattenHOL_length_eq_sizeOfShapeHOL value hwf
  have hsize : sizeOfShapeHOL (shapeOfHOLExact value) ≤ 32 := by
    have h := hcond.2
    rw [hstate.2.2.2.1, sizeOfShapeWithContextHOL_eq _ _ hwf] at h
    exact h
  let temps := decCallSlots ctxt (shapeOfHOLExact value)
  have hnodup : temps.Nodup := decCallSlots_nodup ctxt _
  have htlen : temps.length = es.length := by simp [temps, decCallSlots, hlen]
  have htflen : temps.length = (flattenHOL value).length := by
    simp [temps, decCallSlots, hflen]
  have hdist : distinctListsHol temps (es.flatMap crepExpVarsHOL) = true := by
    simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq]
    intro x hx hmem
    have hmem' : x ∈ (compileExpExactHOLW ctxt e).1.flatMap crepExpVarsHOL := by
      rw [hc]; exact hmem
    obtain ⟨src, sh', slots, hlk, hslot⟩ := (compileExpExactHOLW_vars_from_context ctxt).1 e x hmem'
    have := hlocals.2.1.2 src sh' slots hlk x hslot
    have := (decCallSlots_gt ctxt _ x hx).1
    omega
  let G := t.globals.updateListEq
    (((List.range (flattenHOL value).length).map (fun x => (0 : BitVec 5) + BitVec.ofNat 5 x)).zip
      (flattenHOL value))
  have hcomp : compileProgExactHOLW ctxt (.raise eid e) =
      .seq (nestedDecsHOL temps es
          (crepNestedSeqHOL (storeGlobalsHOL (0 : BitVec 5) (temps.map CrepExpHOL.var))))
        (.raise n) := by
    simp only [compileProgExactHOLW, compileRaiseExactHOLW, hn, hc]
    rw [if_neg (by rw [← hlen]; simp)]
  have hnd := evalNestedDecsSeqResVarEqHOL es temps t (flattenHOL value)
    (crepNestedSeqHOL (storeGlobalsHOL (0 : BitVec 5) (temps.map CrepExpHOL.var)))
    ⟨hev, htlen, hdist, hnodup⟩
  rw [evaluateSeqStoreGlobalsResHOL temps (flattenHOL value) t 0
    ⟨hnodup, htflen, by simp [hflen, hsize]⟩] at hnd
  dsimp only at hnd
  rw [resVarLookupOriginalEqHOL temps (flattenHOL value) t.locals ⟨hnodup, htflen⟩] at hnd
  have htgt : evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt (.raise eid e)) =
      (some (.exception n), CrepSemHOLState.emptyLocals { t with globals := G }) := by
    rw [hcomp, evalCrepSemHOLProgExact_seq_holShape, hnd]
    dsimp only
    rw [if_pos rfl, evalCrepSemHOLProgExact_raise]
  refine ⟨_, _, htgt, ?_, hcode, hexcp, ?_⟩
  · simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.emptyLocalsHOLFinite,
      CrepSemHOLState.emptyLocals] using hstate
  · simp only [pcCompileCorrectResultRel, hn]
    refine ⟨by first | rfl | trivial, fun _ => ⟨?_, hsize⟩⟩
    simp only [globalsLookupHOL, CrepSemHOLState.emptyLocals, G]
    rw [← hflen]
    have hmap : (List.range (flattenHOL value).length).map
          (fun x => (0 : BitVec 5) + BitVec.ofNat 5 x) =
        (List.range (flattenHOL value).length).map (fun x => BitVec.ofNat 5 x) := by
      simp
    rw [hmap]
    exact mapM_lookup_updateListEq _ _ _ (globalAddrs_nodup _ (by rw [hflen]; exact hsize))
      (by simp)

namespace PcCompileCorrectRaiseWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Raise case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectRaiseWitnesses

/-- HOL `pc_compile_correct`, `Raise` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:2071`).
    HOL's printed `evaluate_ind` Raise conjunct is `!eid e s. P (Raise eid e,s)`, with no IH.
    `P` is HOL's induction predicate, unfolded as in `pcCompileCorrectAtHOL`. The
    translation is the one reviewed for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Raise {width : Nat} {σ : Type} [NeZero width] :
    ∀ (eid : MlS) (e : ExpHOL width) (s : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.raise eid e : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.raise eid e : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.raise eid e : ProgHOL width)) =
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
  intro eid e s res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_raise eid e s res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
