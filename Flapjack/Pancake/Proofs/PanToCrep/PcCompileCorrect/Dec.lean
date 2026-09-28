import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.DecCall

/-!
# `pc_compile_correct` Dec case over the exact carriers

The `Dec v sh e prog` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:1506-1724`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_Dec` (bead `flapjack-pxn.18.4.3.99`).

`compile ctxt (Dec v sh e prog)` declares fresh slots
`GENLIST (λx. ctxt.vmax + SUC x) (size_of_shape shape)` initialised to the
compiled `e` and compiles `prog` under the context that binds `v` to them. This
is the same slot allocation as DecCall, so the proof reuses `decCallSlots`,
`decCallCtxt`, and `decCallLocalsRestore` from the DecCall case.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL StructContextExact
  isWfShapeExactHOL)

/-- The continuation of a fresh-slot declaration (Dec, DecCall) leaves the
    caller-context slots of the declared name unchanged when it completes with
    NONE, Continue, or Break. HOL proves this inline with
    `unassigned_free_vars_evaluate_same` and `not_mem_context_assigned_mem_gt`. -/
theorem decCallCtxtContinuationSame {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (v : MlS) (shape : ShapeHOL)
    (sl : HolFiniteMapExact MlS (ValueHOL width)) (tl : HolFiniteMapExact Nat (HolWordLab width))
    (ws : List (HolWordLab width)) (tc : CrepSemHOLState width σ) (prog : ProgHOL width)
    (res2' : Option (CrepResultHOLExact width)) (t2 : CrepSemHOLState width σ)
    (hlocals : panToCrepLocalsRelFiniteExact ctxt sl tl)
    (hmax' : ctxtMaxFiniteExact (decCallCtxt ctxt v shape).vmax (decCallCtxt ctxt v shape).vars)
    (htc : tc.locals = tl.updateListEq ((decCallSlots ctxt shape).zip ws))
    (hrun2 : evalCrepSemHOLProgExact tc (compileProgExactHOLW (decCallCtxt ctxt v shape) prog) =
      (res2', t2))
    (hform : res2' = none ∨ res2' = some (.continue 0) ∨ res2' = some (.break 0)) :
    ∀ sh ns x, ctxt.vars.lookup v = some (sh, ns) → x ∈ ns → t2.locals.lookup x = tl.lookup x := by
  intro sh ns x hv hx
  have hxle : x ≤ ctxt.vmax := hlocals.2.1.2 v sh ns hv x hx
  have hxnot : x ∉ decCallSlots ctxt shape := fun hm => by
    have := (decCallSlots_gt ctxt shape x hm).1; omega
  have hnot := notMemContextAssignedMemGtHOL (decCallCtxt ctxt v shape) prog x
    ⟨hmax', fun v' sh' ns' hv' hx' => by
      by_cases hvv : v' = v
      · subst hvv
        rw [decCallCtxt_lookup_eq] at hv'
        simp only [Option.some.injEq, Prod.mk.injEq] at hv'
        rw [← hv'.2] at hx'
        exact hxnot hx'
      · rw [decCallCtxt_lookup_ne ctxt v shape v' hvv] at hv'
        exact hvv (hlocals.1.2 v' v sh' sh ns' ns hv' hv ⟨x, hx', hx⟩),
      Nat.le_trans hxle (Nat.le_add_right _ _)⟩
  have := crepUnassignedFreeVarsEvaluateSameHOL _ _ res2' t2 x 0 ⟨hrun2, hform, hnot⟩
  rw [this, htc]
  exact lookup_updateListEq_zip_not_mem tl _ ws x hxnot

/-- The caller's `pc_compile_correct` result relation after a fresh-slot
    declaration (Dec, DecCall): the source restores the declared name with
    `res_var` and the target restores the slots with the `nested_decs` fold. -/
theorem decCallCtxtResultRestore {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (v : MlS) (shape : ShapeHOL)
    (sl : HolFiniteMapExact MlS (ValueHOL width)) (tl : HolFiniteMapExact Nat (HolWordLab width))
    (s2 : PanSemStateFiniteExact width σ) (t2 : CrepSemHOLState width σ)
    (res2 : Option (PanSemResultExact width)) (res2' : Option (CrepResultHOLExact width))
    (hlocals : panToCrepLocalsRelFiniteExact ctxt sl tl)
    (hrr2 : pcCompileCorrectResultRel (decCallCtxt ctxt v shape) s2 t2 res2 res2')
    (hsame : res2' = none ∨ res2' = some (.continue 0) ∨ res2' = some (.break 0) →
      ∀ sh ns x, ctxt.vars.lookup v = some (sh, ns) → x ∈ ns → t2.locals.lookup x = tl.lookup x) :
    pcCompileCorrectResultRel ctxt
      { s2 with locals := HolFiniteMapExact.resVarEq s2.locals (v, sl.lookup v) }
      { t2 with locals :=
        (((decCallSlots ctxt shape).zip ((decCallSlots ctxt shape).map tl.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry) t2.locals) }
      res2 res2' := by
  rcases res2 with _ | r2
  · obtain ⟨rfl, hl2⟩ := hrr2
    exact ⟨rfl, decCallLocalsRestore ctxt v shape sl tl _ _ hlocals hl2 (hsame (Or.inl rfl))⟩
  cases r2 with
  | error => exact hrr2.elim
  | «break» =>
      obtain ⟨rfl, hl2⟩ := hrr2
      exact ⟨rfl, decCallLocalsRestore ctxt v shape sl tl _ _ hlocals hl2
        (hsame (Or.inr (Or.inr rfl)))⟩
  | «continue» =>
      obtain ⟨rfl, hl2⟩ := hrr2
      exact ⟨rfl, decCallLocalsRestore ctxt v shape sl tl _ _ hlocals hl2
        (hsame (Or.inr (Or.inl rfl)))⟩
  | timeOut => exact hrr2
  | returned rv => exact hrr2
  | finalFfi f => exact hrr2
  | exception eid ev =>
      simp only [pcCompileCorrectResultRel] at hrr2 ⊢
      split at hrr2
      · exact hrr2.elim
      exact ⟨hrr2.1, fun hsize => by simpa [globalsLookupHOL] using hrr2.2 hsize⟩

/-- HOL `pc_compile_correct[Dec]` (`pan_to_crepProofScript.sml:1506-1724`) against
    `pcCompileCorrectAt`, from the Dec IH of the rebound `evaluate_ind` (`P` for
    the body after `v` is bound to the initial value). By the tagged
    `compile_exp_val_rel`, the compiled initialiser evaluates to `flatten value`,
    so `nested_decs` installs it in the fresh slots, and `locals_rel_extend_new_var`
    gives the body's `locals_rel`. After the body, the source `res_var` and the
    target slot restoration re-establish the caller's relations. A failed
    initialiser or a shape mismatch is a source Error, excluded by
    `res ≠ SOME Error`. No target run is assumed. Untagged: the tagged HOL-shaped
    statement is `pcCompileCorrect_Dec`. -/
theorem pcCompileCorrectAt_dec {width : Nat} {σ : Type} [NeZero width]
    (v : MlS) (sh : ShapeHOL) (e : ExpHOL width) (prog : ProgHOL width)
    (source : PanSemStateFiniteExact width σ)
    (ih : ∀ value : ValueHOL width,
      @evalHOLExact width σ _ source.toExact
          (fun address => Classical.propDecidable (source.memaddrs address)) e = some value →
      sh = shapeOfHOLExact value →
      pcCompileCorrectAt prog { source with locals := source.locals.update (v, value) }) :
    pcCompileCorrectAt (.dec v sh e prog : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocs : localisedExpHOL e = true ∧ localisedProgHOL prog = true := by
    simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  cases heval : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) e with
  | none =>
      rw [heval] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some value =>
  rw [heval] at hrun
  dsimp only at hrun
  by_cases hsh : shapeEqHOL sh (shapeOfHOLExact value) = true
  case neg =>
    rw [if_neg hsh] at hrun
    exact absurd (Prod.mk.inj hrun).1.symm hres
  rw [if_pos hsh] at hrun
  have hshape : sh = shapeOfHOLExact value := (shapeEqHOL_eq_true _ _).mp hsh
  rcases hc : compileExpExactHOLW ctxt e with ⟨es, cs⟩
  obtain ⟨hes, hlen, hcs, hwf⟩ :=
    @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) ctxt t
      (fun address => Classical.propDecidable (t.memaddrs address))
      e value es cs heval hstate hcode hlocals hlocs.1 hc
  subst hcs
  have hnodup := decCallSlots_nodup ctxt (shapeOfHOLExact value)
  have hflen : (flattenHOL value).length = sizeOfShapeHOL (shapeOfHOLExact value) :=
    flattenHOL_length_eq_sizeOfShapeHOL value hwf
  have hslen : (decCallSlots ctxt (shapeOfHOLExact value)).length = es.length := by
    simp [decCallSlots, hlen]
  have hdist : distinctListsHol (decCallSlots ctxt (shapeOfHOLExact value))
      (es.flatMap crepExpVarsHOL) = true := by
    simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq]
    intro x hx hmem
    have hmem' : x ∈ (compileExpExactHOLW ctxt e).1.flatMap crepExpVarsHOL := by
      rw [hc]; exact hmem
    obtain ⟨src, sh', slots, hlk, hslot⟩ := (compileExpExactHOLW_vars_from_context ctxt).1 e x hmem'
    have := hlocals.2.1.2 src sh' slots hlk x hslot
    have := (decCallSlots_gt ctxt _ x hx).1
    omega
  have hcomp : compileProgExactHOLW ctxt (.dec v sh e prog) =
      nestedDecsHOL (decCallSlots ctxt (shapeOfHOLExact value)) es
        (compileProgExactHOLW (decCallCtxt ctxt v (shapeOfHOLExact value)) prog) := by
    simp only [compileProgExactHOLW, compileDecExactHOLW, hc]
    rw [if_neg (by rw [← hlen]; simp)]
  have hnd := evalNestedDecsSeqResVarEqHOL es (decCallSlots ctxt (shapeOfHOLExact value)) t
    (flattenHOL value)
    (compileProgExactHOLW (decCallCtxt ctxt v (shapeOfHOLExact value)) prog)
    ⟨hes, hslen, hdist, hnodup⟩
  rcases hcont : (PanSemStateFiniteExact.setVarHOLFinite v value source).evaluateHOLFiniteState
      prog with ⟨res2, s2⟩
  rw [hcont] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  have hlocc := localsRelExtendNewVarHOL ctxt source.locals t.locals value v
    (decCallSlots ctxt (shapeOfHOLExact value))
    ⟨hlocals, hwf, hnodup, fun y hy => decCallSlots_gt ctxt _ y hy,
      by simp [decCallSlots]⟩
  obtain ⟨res2', t2, hrun2, hs2, hc2, he2, hrr2⟩ :=
    ih value heval hshape res2 s2
      { t with locals := (t.locals.updateListEq
          ((decCallSlots ctxt (shapeOfHOLExact value)).zip (flattenHOL value))) }
      (decCallCtxt ctxt v (shapeOfHOLExact value)) hcont hres
      (by simpa [panToCrepStateRelFiniteExact] using hstate) hcode hexcp hlocc hlocs.2
  rw [hrun2] at hnd
  rw [hcomp, hnd]
  refine ⟨res2', _, rfl, ?_, hc2, he2, ?_⟩
  · simpa [panToCrepStateRelFiniteExact] using hs2
  · exact decCallCtxtResultRestore ctxt v (shapeOfHOLExact value) source.locals t.locals s2 t2
      res2 res2' hlocals hrr2
      (fun hform => decCallCtxtContinuationSame ctxt v (shapeOfHOLExact value) source.locals
        t.locals (flattenHOL value) _ prog res2' t2 hlocals hlocc.2.1 rfl hrun2 hform)

namespace PcCompileCorrectDecWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Dec case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectDecWitnesses

/-- HOL `pc_compile_correct`, `Dec` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:1506`).
    HOL's printed `evaluate_ind` Dec conjunct is
    `!v sh e prog s. (!value. eval s e = SOME value /\ sh = shape_of value ==>
      P (prog,s with locals := fmupdate v value s.locals)) ==> P (Dec v sh e prog,s)`;
    the IH is transcribed binder for binder, at `P = pcCompileCorrectAtHOL`.
    `eval s` is the tagged exact expression evaluator with the classical address
    decision, as in the tagged Pan Dec arm (`evaluateHOLFiniteState_dec_total`),
    and `fmupdate v value` is the finite map's `update (v, value)` (`FUPDATE`).
    The conclusion is `P (Dec v sh e prog, s)` unfolded as in
    `pcCompileCorrectAtHOL`. The translation is the one reviewed for
    `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Dec {width : Nat} {σ : Type} [NeZero width] :
    ∀ (v : MlS) (sh : ShapeHOL) (e : ExpHOL width) (prog : ProgHOL width)
      (s : PanSemStateFiniteExact width σ),
      (∀ value : ValueHOL width,
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some value ∧
            sh = shapeOfHOLExact value →
          pcCompileCorrectAtHOL prog { s with locals := s.locals.update (v, value) }) →
      ∀ (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.dec v sh e prog : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.dec v sh e prog : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.dec v sh e prog : ProgHOL width)) =
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
  intro v sh e prog s ih res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_dec v sh e prog s
      (fun value hv hsh => (pcCompileCorrectAt_iff_HOL _ _).mpr (ih value ⟨hv, hsh⟩))
      res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
