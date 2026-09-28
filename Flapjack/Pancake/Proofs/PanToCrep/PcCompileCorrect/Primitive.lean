import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assign
import Flapjack.Pancake.Proofs.PanToCrep.Primop

/-!
# `pc_compile_correct` Primitive case over the exact carriers

The `Primitive v pop es` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:1115-1270`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_Primitive` (bead `flapjack-pxn.18.4.3.106`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL StructContextExact
  isWfShapeExactHOL)

private theorem isSome_of_mapM_some {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ x, x ∈ xs → (f x).isSome
  | [], _, _, x, hx => by simp at hx
  | y :: xs, ys, h, x, hx => by
      simp only [List.mapM_cons] at h
      cases hy : f y with
      | none => simp [hy] at h
      | some b =>
          cases hxs : xs.mapM f with
          | none => simp [hy, hxs] at h
          | some zs =>
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · simp [hy]
              · exact isSome_of_mapM_some f xs zs hxs x hx

/-- HOL `pc_compile_correct[Primitive]` (`pan_to_crepProofScript.sml:1115-1270`)
    against `pcCompileCorrectAt`. The source evaluates the arguments to `vs`,
    `pan_primop pop vs = SOME value`, and writes `value` to the existing local
    `v` of the same shape. The compiled arguments evaluate to
    `FLAT (MAP flatten vs)` (the tagged `eval_map_comp_exp_flat_eq`) and are held
    in fresh temporaries. The target `Primitive ns pop temps` then computes
    `flatten value` (the tagged `pan_primop_crep_primop`) into `v`'s slots `ns`.
    Restoring the temporaries leaves exactly `ns` updated. A failed evaluation,
    primop, or destination check is a source Error, excluded by
    `res ≠ SOME Error`. No target run is assumed. Untagged: the tagged HOL-shaped
    statement is `pcCompileCorrect_Primitive`. -/
theorem pcCompileCorrectAt_primitive {width : Nat} {σ : Type} [NeZero width]
    (v : MlS) (pop : PrimOp) (es : List (ExpHOL width)) (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.primitive v pop es : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hloces : everyExpListHOL localisedExpHOL es = true := by
    simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_primitive] at hrun
  cases hargs : @evalListHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) es with
  | none =>
      rw [hargs] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some vs =>
  rw [hargs] at hrun
  dsimp only at hrun
  cases hprim : panPrimopHOLExact pop vs with
  | none =>
      rw [hprim] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some value =>
  rw [hprim] at hrun
  dsimp only at hrun
  split at hrun
  case isFalse => exact absurd (Prod.mk.inj hrun).1.symm hres
  rename_i hvalid
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  cases hold : source.locals.lookup v with
  | none =>
      simp [PanSemStateFiniteExact.isValidValueHOLFinite,
        PanSemStateFiniteExact.lookupKvarHOLFinite, hold] at hvalid
  | some old =>
  have hse : shapeOfHOLExact value = shapeOfHOLExact old := by
    have : shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact old) = true := by
      simpa [PanSemStateFiniteExact.isValidValueHOLFinite,
        PanSemStateFiniteExact.lookupKvarHOLFinite, hold] using hvalid
    exact (shapeEqHOL_eq_true _ _).mp this
  obtain ⟨ns, ws, hvar, hmm, hfl, hwfo⟩ := hlocals.2.2 v old hold
  have hnodup : ns.Nodup := hlocals.1.1 _ _ _ hvar
  have hle : ∀ k, k ∈ ns → k ≤ ctxt.vmax := hlocals.2.1.2 v _ ns hvar
  have hnslen : ns.length = (flattenHOL old).length := by
    rw [opt_mmap_length_eq _ _ _ hmm, ← hfl]
  have hflo := flattenHOL_length_eq_sizeOfShapeHOL old hwfo
  have hwfv : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
    rw [hse]; exact hwfo
  have hflv := flattenHOL_length_eq_sizeOfShapeHOL value hwfv
  have hnsv : ns.length = (flattenHOL value).length := by rw [hnslen, hflo, ← hse, hflv]
  -- target arguments
  let ces := (compileExpExactHOLWList ctxt es).flatMap Prod.fst
  let flat := vs.flatMap flattenHOL
  have hcargs : ces.mapM (@evalCrepSemHOLExp width _ σ t
      (fun address => Classical.propDecidable (t.memaddrs address))) = some flat :=
    pcCompileCorrectCallTargetArgs source t ctxt es vs
      (by simpa [PanSemStateFiniteExact.evalListHOLFinite] using hargs) hstate hcode hlocals
      hloces
  have hces := map_eq_of_mapM_eq_some _ _ _ hcargs
  have hclen : ces.length = flat.length := by
    have := congrArg List.length hces; simpa using this
  let temps := (List.range ces.length).map (fun index => ctxt.vmax + index + 1)
  have htnodup : temps.Nodup :=
    List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
  have htgt : ∀ k, k ∈ temps → ctxt.vmax < k := by
    intro k hk
    simp only [temps, List.mem_map, List.mem_range] at hk
    obtain ⟨i, _, rfl⟩ := hk
    omega
  have htlen : temps.length = ces.length := by simp [temps]
  have htflen : temps.length = flat.length := by rw [htlen, hclen]
  have hdisj : ∀ k, k ∈ temps → k ∉ ns := fun k hk hn => by
    have := htgt k hk; have := hle k hn; omega
  have hdist : distinctListsHol temps (ces.flatMap crepExpVarsHOL) = true := by
    simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq]
    intro x hx hmem
    obtain ⟨src, sh', slots, hlk, hslot⟩ :=
      (compileExpExactHOLW_vars_from_context ctxt).2 es x hmem
    have := hlocals.2.1.2 src sh' slots hlk x hslot
    have := htgt x hx
    omega
  have hcomp : compileProgExactHOLW ctxt (.primitive v pop es) =
      nestedDecsHOL temps ces (.primitive ns pop temps) := by
    simp only [compileProgExactHOLW, compilePrimitiveExactHOLW, hvar]
    rfl
  have hnd := evalNestedDecsSeqResVarEqHOL ces temps t flat (.primitive ns pop temps)
    ⟨hces, htlen, hdist, htnodup⟩
  have hcrep := panPrimopCrepPrimopExactHOL pop vs value hprim
  let tl' := t.locals.updateListEq (temps.zip flat)
  have htargs : temps.mapM tl'.lookup = some flat :=
    mapM_lookup_updateListEq t.locals temps flat htnodup htflen
  have hnsSome : ∀ k, k ∈ ns → (tl'.lookup k).isSome := by
    intro k hk
    rw [lookup_updateListEq_zip_not_mem t.locals temps flat k (fun h => hdisj k h hk)]
    exact isSome_of_mapM_some _ _ _ hmm k hk
  have hprimRun : evalCrepSemHOLProgExact { t with locals := tl' } (.primitive ns pop temps) =
      (none, { t with locals := tl'.updateListEq (ns.zip (flattenHOL value)) }) := by
    rw [evalCrepSemHOLProgExact_primitive_holShape]
    simp only [htargs]
    rw [show crepPrimopHOLExact pop flat = some (flattenHOL value) from hcrep]
    dsimp only
    rw [if_pos ⟨hnsv, hnsSome, hnodup⟩]
  rw [hprimRun] at hnd
  have hfinal : ((temps.zip (temps.map t.locals.lookup)).foldl
        (fun current entry => HolFiniteMapExact.resVarEq current entry)
        (tl'.updateListEq (ns.zip (flattenHOL value)))) =
      t.locals.updateListEq (ns.zip (flattenHOL value)) := by
    have hmapEq : temps.map t.locals.lookup =
        temps.map (t.locals.updateListEq (ns.zip (flattenHOL value))).lookup := by
      apply List.map_congr_left
      intro k hk
      exact (lookup_updateListEq_zip_not_mem t.locals ns _ k (hdisj k hk)).symm
    simp only [tl']
    rw [updateListEq_zip_comm t.locals temps ns flat (flattenHOL value) htflen hnsv hdisj,
      hmapEq]
    exact resVarLookupOriginalEqHOL temps flat _ ⟨htnodup, htflen⟩
  have htgt' : evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt (.primitive v pop es)) =
      (none, { t with locals := t.locals.updateListEq (ns.zip (flattenHOL value)) }) := by
    rw [hcomp, hnd]
    dsimp only
    rw [hfinal]
  refine ⟨none, _, htgt', ?_, hcode, hexcp, rfl, ?_⟩
  · simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.setVarHOLFinite] using hstate
  · have hvar' : ctxt.vars.lookup v = some (shapeOfHOLExact value, ns) := by rw [hvar, hse]
    have hlr := panToCrepLocalsRelFiniteExact_setVar ctxt source.locals t.locals v value ns
      hlocals hvar' hnsv hwfv
    have hupd : source.locals.update (v, value) = source.locals.updateEq (v, value) := by
      apply HolFiniteMapExact.ext
      funext k
      simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL_eq_FUPDATE]
    simpa [PanSemStateFiniteExact.setVarHOLFinite, hupd] using hlr

namespace PcCompileCorrectPrimitiveWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Primitive case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectPrimitiveWitnesses

/-- HOL `pc_compile_correct`, `Primitive` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:1115`).
    HOL's printed `evaluate_ind` Primitive conjunct is
    `!v pop es s. P (Primitive v pop es,s)`, with no IH. `P` is HOL's induction
    predicate, unfolded as in `pcCompileCorrectAtHOL`. The translation is the one
    reviewed for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Primitive {width : Nat} {σ : Type} [NeZero width] :
    ∀ (v : MlS) (pop : PrimOp) (es : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.primitive v pop es : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.primitive v pop es : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.primitive v pop es : ProgHOL width)) =
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
  intro v pop es s res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_primitive v pop es s res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
