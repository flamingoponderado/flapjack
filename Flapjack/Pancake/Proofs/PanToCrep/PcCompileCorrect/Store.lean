import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.DecCall

/-!
# `pc_compile_correct` Store case over the exact carriers

The `Store dst src` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:1726-1856`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_Store` (bead `flapjack-pxn.18.4.3.107`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL StructContextExact
  isWfShapeExactHOL)

/-- HOL `pc_compile_correct[Store]` (`pan_to_crepProofScript.sml:1726-1856`)
    against `pcCompileCorrectAt`. The source evaluates `dst` to `Word addr` and
    `src` to `value`, and `mem_stores addr (flatten value)` succeeds. By the
    tagged `compile_exp_val_rel`, the compiled address is a single expression
    evaluating to `Word addr` and the compiled value evaluates to
    `flatten value`. They are held in fresh temporaries `ad :: temps`
    (`eval_nested_decs_seq_res_var_eq`), and the store sequence writes exactly
    the source memory (`evaluate_seq_stores_mem_state_rel`) without touching
    locals (`evaluate_seq_stroes_locals_eq`). Restoring the temporaries gives
    back the caller's locals (`res_var_lookup_original_eq`). Every other
    outcome is a source Error, excluded by `res ≠ SOME Error`. No target run
    is assumed. Untagged: the tagged HOL-shaped statement is
    `pcCompileCorrect_Store`. -/
theorem pcCompileCorrectAt_store {width : Nat} {σ : Type} [NeZero width]
    (dst src : ExpHOL width) (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.store dst src : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocs : localisedExpHOL dst = true ∧ localisedExpHOL src = true := by
    simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_store] at hrun
  split at hrun
  case h_2 => exact absurd (Prod.mk.inj hrun).1.symm hres
  rename_i addr hdst
  cases hsrc : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) src with
  | none =>
      rw [hsrc] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some value =>
  rw [hsrc] at hrun
  dsimp only at hrun
  cases hms : @panMemStoresHOL width _ addr (flattenHOL value) source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.memory with
  | none =>
      rw [hms] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some m =>
  rw [hms] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  -- the compiled address
  rcases hcd : compileExpExactHOLW ctxt dst with ⟨des, dsh⟩
  obtain ⟨hdes, _, _, _⟩ :=
    @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) ctxt t
      (fun address => Classical.propDecidable (t.memaddrs address))
      dst (.val (.word addr)) des dsh hdst hstate hcode hlocals hlocs.1 hcd
  obtain ⟨ca, hca⟩ : ∃ ca, des = [ca] := by
    rcases des with _ | ⟨ca, _ | ⟨_, _⟩⟩
    · simp [flattenHOL] at hdes
    · exact ⟨ca, rfl⟩
    · simp [flattenHOL] at hdes
  subst hca
  -- the compiled value
  rcases hc : compileExpExactHOLW ctxt src with ⟨es, sh⟩
  obtain ⟨hes, hlen, hsh, hwf⟩ :=
    @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) ctxt t
      (fun address => Classical.propDecidable (t.memaddrs address))
      src value es sh hsrc hstate hcode hlocals hlocs.2 hc
  subst hsh
  have hflen : (flattenHOL value).length = sizeOfShapeHOL (shapeOfHOLExact value) :=
    flattenHOL_length_eq_sizeOfShapeHOL value hwf
  let ad := ctxt.vmax + 1
  let temps := (List.range (sizeOfShapeHOL (shapeOfHOLExact value))).map
    (fun index => ad + index + 1)
  have htemps_gt : ∀ k, k ∈ temps → ad < k := by
    intro k hk
    simp only [temps, List.mem_map, List.mem_range] at hk
    obtain ⟨i, _, rfl⟩ := hk
    omega
  have hadtemps : ad ∉ temps := fun h => by have := htemps_gt ad h; omega
  have htnodup : temps.Nodup :=
    List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
  have hallnodup : (ad :: temps).Nodup := List.nodup_cons.mpr ⟨hadtemps, htnodup⟩
  have htflen : temps.length = (flattenHOL value).length := by simp [temps, hflen]
  have hvars : ∀ x, x ∈ (ca :: es).flatMap crepExpVarsHOL → x ≤ ctxt.vmax := by
    intro x hx
    simp only [List.flatMap_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · have hx' : x ∈ (compileExpExactHOLW ctxt dst).1.flatMap crepExpVarsHOL := by
        rw [hcd]; simpa using hx
      obtain ⟨n, sh', slots, hlk, hslot⟩ := (compileExpExactHOLW_vars_from_context ctxt).1 dst x hx'
      exact hlocals.2.1.2 n sh' slots hlk x hslot
    · have hx' : x ∈ (compileExpExactHOLW ctxt src).1.flatMap crepExpVarsHOL := by
        rw [hc]; exact hx
      obtain ⟨n, sh', slots, hlk, hslot⟩ := (compileExpExactHOLW_vars_from_context ctxt).1 src x hx'
      exact hlocals.2.1.2 n sh' slots hlk x hslot
  have hdist : distinctListsHol (ad :: temps) ((ca :: es).flatMap crepExpVarsHOL) = true := by
    simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq]
    intro x hx hmem
    have := hvars x hmem
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [ad] at this; omega
    · have := htemps_gt x hx; simp only [ad] at *; omega
  have hmap : (ca :: es).map (@evalCrepSemHOLExp width _ σ t
      (fun address => Classical.propDecidable (t.memaddrs address))) =
      (HolWordLab.word addr :: flattenHOL value).map some := by
    simp only [List.map_cons]
    simp only [flattenHOL, List.map_cons, List.map_nil, List.cons.injEq] at hdes
    rw [hdes.1, hes]
  let body : CrepProgHOL width :=
    crepNestedSeqHOL (storesHOL (.var ad) (temps.map CrepExpHOL.var) (0 : BitVec width))
  have hcomp : compileProgExactHOLW ctxt (.store dst src) =
      nestedDecsHOL (ad :: temps) (ca :: es) body := by
    simp only [compileProgExactHOLW, compileStoreExactHOLW, hcd, hc]
    rw [if_neg (by rw [← hlen]; simp)]
  have hnd := evalNestedDecsSeqResVarEqHOL (ca :: es) (ad :: temps) t
    (HolWordLab.word addr :: flattenHOL value) body
    ⟨hmap, by simp [temps, hlen], hdist, hallnodup⟩
  rcases hb : evalCrepSemHOLProgExact
      { t with locals := (t.locals.updateListEq
          ((ad :: temps).zip (HolWordLab.word addr :: flattenHOL value))) } body with ⟨q, r⟩
  rw [hb] at hnd
  have hmem : @panMemStoresHOL width _ (addr + 0) (flattenHOL value) t.memaddrs
      (fun x => Classical.propDecidable (t.memaddrs x)) t.memory = some m := by
    rw [show addr + (0 : BitVec width) = addr by simp, ← hstate.1, ← hstate.2.1]
    exact hms
  obtain ⟨hq, hrm, hrma, hrsh, hrbe, hrffi, hrcode, hrclk, hrba, hrta⟩ :=
    evaluateSeqStoresMemStateRelHOL temps (flattenHOL value) ad 0 t q r addr m
      ⟨htflen, hadtemps, htnodup, hmem, hb⟩
  have hrl := evaluateSeqStoresLocalsEqHOL _ _ _ _ q r hb
  have hloc' : ((ad :: temps).zip ((ad :: temps).map t.locals.lookup)).foldl
      (fun current entry => HolFiniteMapExact.resVarEq current entry) r.locals = t.locals := by
    rw [hrl]
    exact resVarLookupOriginalEqHOL (ad :: temps) (HolWordLab.word addr :: flattenHOL value)
      t.locals ⟨hallnodup, by simp [htflen]⟩
  refine ⟨q, _, by rw [hcomp]; exact hnd, ?_, ?_, hexcp, ?_⟩
  · refine ⟨hrm.symm, hstate.2.1.trans hrma.symm, hstate.2.2.1.trans hrsh.symm,
      hstate.2.2.2.1, hstate.2.2.2.2.1, hstate.2.2.2.2.2.1.trans hrclk.symm,
      hstate.2.2.2.2.2.2.1.trans hrbe.symm, hstate.2.2.2.2.2.2.2.1.trans hrffi.symm,
      hstate.2.2.2.2.2.2.2.2.1.trans hrba.symm, hstate.2.2.2.2.2.2.2.2.2.trans hrta.symm⟩
  · show codeRelExactHOLW ctxt source.code r.code
    rw [hrcode]; exact hcode
  · subst hq
    refine ⟨rfl, ?_⟩
    show panToCrepLocalsRelFiniteExact ctxt source.locals
      (((ad :: temps).zip ((ad :: temps).map t.locals.lookup)).foldl
        (fun current entry => HolFiniteMapExact.resVarEq current entry) r.locals)
    rw [hloc']
    exact hlocals

namespace PcCompileCorrectStoreWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Store case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectStoreWitnesses

/-- HOL `pc_compile_correct`, `Store` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:1726`).
    HOL's printed `evaluate_ind` Store conjunct is `!dst src s. P (Store dst src,s)`,
    with no IH. `P` is HOL's induction predicate, unfolded as in
    `pcCompileCorrectAtHOL`. The translation is the one reviewed for
    `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Store {width : Nat} {σ : Type} [NeZero width] :
    ∀ (dst src : ExpHOL width) (s : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.store dst src : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.store dst src : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.store dst src : ProgHOL width)) =
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
  intro dst src s res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_store dst src s res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
