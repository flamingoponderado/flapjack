import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.DecCall
import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedAssign

/-!
# `pc_compile_correct` Assign case over the exact carriers

The `Assign vk v src` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:880-1068`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_Assign` (bead `flapjack-pxn.18.4.3.105`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL StructContextExact
  isWfShapeExactHOL)

private theorem fupdListZipMemIndep {β : Type} (k : Nat) :
    ∀ (xs : List Nat) (ys : List β) (f g : FiniteMap Nat β), k ∈ xs → xs.length = ys.length →
      FUPDATE_LIST_HOL f (xs.zip ys) k = FUPDATE_LIST_HOL g (xs.zip ys) k
  | [], _, _, _, hk, _ => by simp at hk
  | _ :: _, [], _, _, _, hlen => by simp at hlen
  | x :: xs, y :: ys, f, g, hk, hlen => by
      rw [List.zip_cons_cons, FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons]
      by_cases hkxs : k ∈ xs
      · exact fupdListZipMemIndep k xs ys _ _ hkxs (by simpa using hlen)
      · have hkx : k = x := by simpa [hkxs] using hk
        rw [fupdateListHOL_zip_not_mem' k xs ys _ hkxs, fupdateListHOL_zip_not_mem' k xs ys _ hkxs]
        simp [FUPDATE_HOL, hkx]

/-- Updates at disjoint key lists commute. -/
theorem updateListEq_zip_comm {β : Type} (m : HolFiniteMapExact Nat β)
    (as bs : List Nat) (xs ys : List β) (hx : as.length = xs.length) (hy : bs.length = ys.length)
    (hdisj : ∀ k, k ∈ as → k ∉ bs) :
    (m.updateListEq (as.zip xs)).updateListEq (bs.zip ys) =
      (m.updateListEq (bs.zip ys)).updateListEq (as.zip xs) := by
  apply HolFiniteMapExact.ext
  funext k
  simp only [HolFiniteMapExact.lookup_updateListEq]
  by_cases hb : k ∈ bs
  · have ha : k ∉ as := fun h => hdisj k h hb
    rw [fupdateListHOL_zip_not_mem' k as xs _ ha]
    exact fupdListZipMemIndep k bs ys _ _ hb hy
  · rw [fupdateListHOL_zip_not_mem' k bs ys _ hb]
    by_cases ha : k ∈ as
    · exact fupdListZipMemIndep k as xs _ _ ha hx
    · simp only [HolFiniteMapExact.lookup_updateListEq, fupdateListHOL_zip_not_mem' k as xs _ ha,
        fupdateListHOL_zip_not_mem' k bs ys _ hb]

theorem map_eq_of_mapM_eq_some {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.map f = ys.map some
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
      simp only [List.mapM_cons] at h
      cases hx : f x with
      | none => simp [hx] at h
      | some y =>
          cases hxs : xs.mapM f with
          | none => simp [hx, hxs] at h
          | some zs =>
              simp [hx, hxs] at h
              subst h
              simp [hx, map_eq_of_mapM_eq_some f xs zs hxs]

theorem mapM_congr_mem'' {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x, x ∈ xs → f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.mapM_cons, h x (by simp),
        mapM_congr_mem'' f g xs (fun y hy => h y (by simp [hy]))]

/-- The target run of `compile ctxt (Assign Local v src)`
    (`pan_to_crepScript.sml:139-157`) when `v`'s slots `ns` are present and
    distinct and the compiled expressions evaluate to `flat`: both compiled arms
    (direct `nested_seq (MAP2 Assign ns es)`, and the same through fresh
    temporaries) end normally with `ns` bound to `flat` and no other local
    changed. HOL proves this inline with `eval_nested_assign_distinct_eq` and
    `eval_nested_decs_seq_res_var_eq`. -/
theorem compileLocalAssignTarget {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (t : CrepSemHOLState width σ) (name : MlS)
    (e : ExpHOL width) (es : List (CrepExpHOL width)) (sh sh' : ShapeHOL)
    (ns : List Nat) (flat ws : List (HolWordLab width))
    (hc : compileExpExactHOLW ctxt e = (es, sh))
    (hvar : ctxt.vars.lookup name = some (sh', ns))
    (hnodup : ns.Nodup) (hle : ∀ k, k ∈ ns → k ≤ ctxt.vmax)
    (hesvars : ∀ k, k ∈ es.flatMap crepExpVarsHOL → k ≤ ctxt.vmax)
    (hns : ns.mapM t.locals.lookup = some ws)
    (hes : es.map (@evalCrepSemHOLExp width _ σ t
      (fun address => Classical.propDecidable (t.memaddrs address))) = flat.map some)
    (hlen : ns.length = es.length) :
    evalCrepSemHOLProgExact t (compileLocalAssignExactHOLW ctxt name e) =
      (none, { t with locals := t.locals.updateListEq (ns.zip flat) }) := by
  classical
  have hflen : flat.length = es.length := by
    have := congrArg List.length hes; simpa using this.symm
  have hvarsEq : (es.flatMap fun c => crepExpVarsW (crepExpOfHOL c)) =
      es.flatMap crepExpVarsHOL := by
    congr 1; funext c
    rw [crepExpVarsW_eq_crepExpVarsHOL_crepExpToHOL, crepExpToHOL_crepExpOfHOL]
  simp only [compileLocalAssignExactHOLW, hc, hvar]
  rw [if_neg (by rw [hlen]; simp)]
  try dsimp only
  rw [hvarsEq]
  split
  · rename_i hdist
    exact evalNestedAssignDistinctEqCrepHOL es ns t flat ws hes hns hdist hnodup hlen
  · let temps := (List.range ns.length).map (fun index => ctxt.vmax + index + 1)
    have htnodup : temps.Nodup :=
      List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
    have htgt : ∀ k, k ∈ temps → ctxt.vmax < k := by
      intro k hk
      simp only [temps, List.mem_map, List.mem_range] at hk
      obtain ⟨i, _, rfl⟩ := hk
      omega
    have htlen : temps.length = es.length := by simp [temps, hlen]
    have htflen : temps.length = flat.length := by rw [htlen, hflen]
    have hdisj : ∀ k, k ∈ temps → k ∉ ns := fun k hk hn => by
      have := htgt k hk; have := hle k hn; omega
    have hdist : distinctListsHol temps (es.flatMap crepExpVarsHOL) = true := by
      simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq]
      intro x hx hmem
      have := htgt x hx; have := hesvars x hmem; omega
    have hnd := evalNestedDecsSeqResVarEqHOL es temps t flat
      (crepNestedSeqHOL (List.zipWith CrepProgHOL.assign ns (temps.map CrepExpHOL.var)))
      ⟨hes, htlen, hdist, htnodup⟩
    let t' : CrepSemHOLState width σ := { t with locals := t.locals.updateListEq (temps.zip flat) }
    have hEval : (temps.map CrepExpHOL.var).map (evalCrepSemHOLExpDefault t') = flat.map some := by
      have hm := mapM_lookup_updateListEq t.locals temps flat htnodup htflen
      rw [List.map_map]
      have := map_eq_of_mapM_eq_some _ _ _ hm
      rw [← this]
      apply List.map_congr_left
      intro k _
      simp [evalCrepSemHOLExpDefault, evalCrepSemHOLExpWithMemDec, evalCrepSemHOLExp, t']
    have hLocals : ns.mapM t'.locals.lookup = some ws := by
      rw [← hns]
      apply mapM_congr_mem''
      intro k hk
      exact lookup_updateListEq_zip_not_mem t.locals temps flat k (fun h => hdisj k h hk)
    have hDist' : distinctListsHol ns
        ((temps.map (CrepExpHOL.var (width := width))).flatMap crepExpVarsHOL) = true := by
      simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq, List.flatMap_map]
      intro x hx hmem
      simp only [crepExpVarsHOL, List.mem_flatMap, List.mem_singleton] at hmem
      obtain ⟨k, hk, rfl⟩ := hmem
      exact hdisj _ hk hx
    have hinner := evalNestedAssignDistinctEqCrepHOL (temps.map CrepExpHOL.var) ns t' flat ws
      hEval hLocals hDist' hnodup (by simp [temps])
    rw [hinner] at hnd
    rw [hnd]
    congr 2
    have hmapEq : temps.map t.locals.lookup =
        temps.map (t.locals.updateListEq (ns.zip flat)).lookup := by
      apply List.map_congr_left
      intro k hk
      exact (lookup_updateListEq_zip_not_mem t.locals ns flat k (hdisj k hk)).symm
    simp only [t']
    rw [updateListEq_zip_comm t.locals temps ns flat flat htflen (by rw [hlen, hflen]) hdisj,
      hmapEq]
    exact resVarLookupOriginalEqHOL temps flat _ ⟨htnodup, htflen⟩

/-- HOL `pc_compile_correct[Assign]` (`pan_to_crepProofScript.sml:880-1068`)
    against `pcCompileCorrectAt`. `localised_prog` excludes global destinations.
    For a local, `is_valid_value` gives the old value's shape, `locals_rel` its
    distinct slots `ns`, and the tagged `compile_exp_val_rel` the compiled
    expressions' values `flatten value`. Both compiled arms bind `ns` to
    `flatten value` (`compileLocalAssignTarget`), which re-establishes
    `locals_rel` for the updated source local. A failed evaluation or an invalid
    destination is a source Error, excluded by `res ≠ SOME Error`. No target run
    is assumed. Untagged: the tagged HOL-shaped statement is
    `pcCompileCorrect_Assign`. -/
theorem pcCompileCorrectAt_assign {width : Nat} {σ : Type} [NeZero width]
    (vk : VarKind) (v : MlS) (src : ExpHOL width) (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.assign vk v src : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  cases vk with
  | global => simp [localisedProgHOL] at hloc
  | «local» =>
  have hloce : localisedExpHOL src = true := by simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign] at hrun
  cases heval : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) src with
  | none =>
      rw [heval] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some ev =>
  rw [heval] at hrun
  dsimp only at hrun
  split at hrun
  case isFalse => exact absurd (Prod.mk.inj hrun).1.symm hres
  rename_i hvalid
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  cases hold : source.locals.lookup v with
  | none =>
      simp [PanSemStateFiniteExact.isValidValueHOLFinite,
        PanSemStateFiniteExact.lookupKvarHOLFinite,
        hold] at hvalid
  | some old =>
  have hse : shapeOfHOLExact ev = shapeOfHOLExact old := by
    have : shapeEqHOL (shapeOfHOLExact ev) (shapeOfHOLExact old) = true := by
      simpa [PanSemStateFiniteExact.isValidValueHOLFinite,
        PanSemStateFiniteExact.lookupKvarHOLFinite,
        hold] using hvalid
    exact (shapeEqHOL_eq_true _ _).mp this
  obtain ⟨ns, ws, hvar, hmm, hfl, hwfo⟩ := hlocals.2.2 v old hold
  rcases hc : compileExpExactHOLW ctxt src with ⟨es, sh⟩
  obtain ⟨hes, hlen, hsh, hwf⟩ :=
    @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) ctxt t
      (fun address => Classical.propDecidable (t.memaddrs address))
      src ev es sh heval hstate hcode hlocals hloce hc
  have hnslen : ns.length = (flattenHOL old).length := by
    rw [opt_mmap_length_eq _ _ _ hmm, ← hfl]
  have hflo := flattenHOL_length_eq_sizeOfShapeHOL old hwfo
  have hwfe : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact ev) = true := by
    rw [hsh]; exact hwf
  have hflen := flattenHOL_length_eq_sizeOfShapeHOL ev hwfe
  have hlenE : ns.length = es.length := by rw [hnslen, hflo, ← hse, hsh, ← hlen]
  have hesvars : ∀ k, k ∈ es.flatMap crepExpVarsHOL → k ≤ ctxt.vmax := by
    intro k hk
    have hk' : k ∈ (compileExpExactHOLW ctxt src).1.flatMap crepExpVarsHOL := by rw [hc]; exact hk
    obtain ⟨src', sh'', slots, hlk, hslot⟩ :=
      (compileExpExactHOLW_vars_from_context ctxt).1 src k hk'
    exact hlocals.2.1.2 src' sh'' slots hlk k hslot
  have htgt := compileLocalAssignTarget ctxt t v src es sh (shapeOfHOLExact old) ns
    (flattenHOL ev) ws hc hvar (hlocals.1.1 _ _ _ hvar) (hlocals.2.1.2 v _ ns hvar) hesvars hmm hes
    hlenE
  have hcomp : compileProgExactHOLW ctxt (.assign .local v src) =
      compileLocalAssignExactHOLW ctxt v src := by
    simp only [compileProgExactHOLW]
  refine ⟨none, { t with locals := t.locals.updateListEq (ns.zip (flattenHOL ev)) },
    by rw [hcomp]; exact htgt, ?_, hcode, hexcp, rfl, ?_⟩
  · simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.setKvarHOLFinite,
      PanSemStateFiniteExact.setVarHOLFinite] using hstate
  · have hvar' : ctxt.vars.lookup v = some (shapeOfHOLExact ev, ns) := by rw [hvar, hse]
    have hlr := panToCrepLocalsRelFiniteExact_setVar ctxt source.locals t.locals v ev ns hlocals
      hvar' (by rw [hnslen, hflo, ← hse, hflen]) hwfe
    have hupd : source.locals.update (v, ev) = source.locals.updateEq (v, ev) := by
      apply HolFiniteMapExact.ext
      funext k
      simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL_eq_FUPDATE]
    simpa [PanSemStateFiniteExact.setKvarHOLFinite, PanSemStateFiniteExact.setVarHOLFinite,
      hupd] using hlr

namespace PcCompileCorrectAssignWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Assign case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectAssignWitnesses

/-- HOL `pc_compile_correct`, `Assign` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:880`).
    HOL's printed `evaluate_ind` Assign conjunct is
    `!vk v src s. P (Assign vk v src,s)`, with no IH. `P` is HOL's induction
    predicate, unfolded as in `pcCompileCorrectAtHOL`. The translation is the one
    reviewed for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Assign {width : Nat} {σ : Type} [NeZero width] :
    ∀ (vk : VarKind) (v : MlS) (src : ExpHOL width) (s : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.assign vk v src : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.assign vk v src : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.assign vk v src : ProgHOL width)) =
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
  intro vk v src s res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_assign vk v src s res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
