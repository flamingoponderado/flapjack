import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call
import Flapjack.Pancake.Proofs.PanToCrep.NotMemContextAssignedMemGt
import Flapjack.Pancake.Semantics.PanProps.ResVar

/-!
# `pc_compile_correct` DecCall case over the exact carriers

The `DecCall rt shape fname argexps prog1` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:4233-4485`), stated against `pcCompileCorrectAt` and
`pcCompileCorrectDecCallIH`, then in HOL's own shape as the tagged
`pcCompileCorrect_DecCall`.

`compile ctxt (DecCall ...)` declares zeroed return slots
`GENLIST (λx. ctxt.vmax + SUC x) (size_of_shape shape)` around
`Seq (Call (SOME (rts, NONE)) fname cargs) (compile nctxt prog1)`, where `nctxt`
binds `rt` to those slots. The proof reuses the Call prelude
(`pcCompileCorrectCallPrelude`) for the callee, `locals_rel_extend_new_var` for
the continuation entry, and `unassigned_free_vars_evaluate_same` with
`not_mem_context_assigned_mem_gt` to show that the continuation leaves the
caller's `rt` slots alone (bead `flapjack-pxn.18.4.3.95`). The helpers are
untagged: HOL proves them inline inside the DecCall case.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL StructContextExact
  isWfShapeExactHOL)

/-- The DecCall return slots `GENLIST (λx. ctxt.vmax + SUC x) (size_of_shape shape)`. -/
abbrev decCallSlots {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (shape : ShapeHOL) : List Nat :=
  (List.range (sizeOfShapeHOL shape)).map (fun i => ctxt.vmax + i + 1)

/-- The DecCall continuation context of `compile_def`
    (`pan_to_crepScript.sml:262-272`). -/
abbrev decCallCtxt {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (rt : MlS) (shape : ShapeHOL) : PanToCrepContextExact width :=
  { ctxt with
    vars := ctxt.vars.update (rt, (shape, decCallSlots ctxt shape))
    vmax := ctxt.vmax + sizeOfShapeHOL shape }

theorem compileDecCallShape {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (rt : MlS) (shape : ShapeHOL) (f : MlS) (args : List (ExpHOL width)) (prog1 : ProgHOL width) :
    compileProgExactHOLW ctxt (.decCall rt shape f args prog1) =
      nestedDecsHOL (decCallSlots ctxt shape)
        (List.replicate (decCallSlots ctxt shape).length (.const (0 : BitVec width)))
        (.seq (.call (some (decCallSlots ctxt shape, none)) f
            ((compileExpExactHOLWList ctxt args).flatMap Prod.fst))
          (compileProgExactHOLW (decCallCtxt ctxt rt shape) prog1)) := by
  simp only [compileProgExactHOLW, compileDecCallExactHOLW]

theorem decCallSlots_nodup {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (shape : ShapeHOL) : (decCallSlots ctxt shape).Nodup :=
  List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))

theorem decCallSlots_gt {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (shape : ShapeHOL) (x : Nat) (hx : x ∈ decCallSlots ctxt shape) :
    ctxt.vmax < x ∧ x ≤ ctxt.vmax + sizeOfShapeHOL shape := by
  simp only [decCallSlots, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  omega

/-- The target run of the compiled DecCall body
    `nested_decs rts (REPLICATE _ (Const 0w)) (Seq (Call (SOME (rts, NONE)) f cargs) B)`
    after a successful argument evaluation, `lookup_code`, and a positive clock. -/
theorem crepNestedDecCallTarget {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ)
    (fname : MlS) (cargs : List (CrepExpHOL width)) (flat : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (rts : List Nat) (B : CrepProgHOL width)
    (hargs : cargs.mapM (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code fname flat flat.length = some (body, locals))
    (hclock : t.clock ≠ 0)
    (hnodup : rts.Nodup)
    (hdist : distinctListsHol rts (cargs.flatMap crepExpVarsHOL) = true) :
    evalCrepSemHOLProgExact t
        (nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec width)))
          (.seq (.call (some (rts, none)) fname cargs) B)) =
      match (match crepCallAfterBody
          { t with locals := (t.locals.updateListEq
              (rts.zip (List.replicate rts.length (HolWordLab.word (0 : BitVec width))))) }
          (some (rts, none))
          (evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body) with
        | (res, s1) => if res = none then evalCrepSemHOLProgExact s1 B else (res, s1)) with
      | (q, r) => (q, { r with locals :=
          ((rts.zip (rts.map t.locals.lookup)).foldl
            (fun current entry => HolFiniteMapExact.resVarEq current entry) r.locals) }) := by
  classical
  let zeros := List.replicate rts.length (HolWordLab.word (0 : BitVec width))
  let t' : CrepSemHOLState width σ := { t with locals := t.locals.updateListEq (rts.zip zeros) }
  have hnd := evalNestedDecsSeqResVarEqHOL
    (List.replicate rts.length (.const (0 : BitVec width))) rts t zeros
    (.seq (.call (some (rts, none)) fname cargs) B)
    ⟨by simp [zeros, evalCrepSemHOLExp], by simp, by
      simp [distinctListsHol, crepExpVarsHOL], hnodup⟩
  have hargs' : cargs.mapM (@evalCrepSemHOLExp width _ σ t'
      (fun address => Classical.propDecidable (t'.memaddrs address))) = some flat :=
    optMmapEvalDistinctListsNotAffectHOL cargs t flat rts zeros
      ⟨hargs, by simp [zeros], hdist⟩
  have hg : ∀ rts' h, (some (rts, none) : Option (List Nat × Option (BitVec width × CrepProgHOL width))) =
      some (rts', h) → rts'.Nodup := by
    intro rts' h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]; exact hnodup
  have hcall := crepCallTarget t' (some (rts, none)) fname cargs flat body locals hargs'
    hlookup hg hclock
  have hentry : ({ decClockCrepSemHOL t' with locals := locals } : CrepSemHOLState width σ) =
      { decClockCrepSemHOL t with locals := locals } := rfl
  rw [hentry] at hcall
  rw [evalCrepSemHOLProgExact_seq_holShape, hcall] at hnd
  exact hnd

/-- The zero-clock target run of the compiled DecCall body: it times out in a
    state that differs from the caller's only in locals. -/
theorem crepNestedDecCallTimeout {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ)
    (fname : MlS) (cargs : List (CrepExpHOL width)) (flat : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (rts : List Nat) (B : CrepProgHOL width)
    (hargs : cargs.mapM (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code fname flat flat.length = some (body, locals))
    (hclock : t.clock = 0)
    (hnodup : rts.Nodup)
    (hdist : distinctListsHol rts (cargs.flatMap crepExpVarsHOL) = true) :
    ∃ t2, evalCrepSemHOLProgExact t
        (nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec width)))
          (.seq (.call (some (rts, none)) fname cargs) B)) = (some .timeOut, t2) ∧
      { t2 with locals := t.locals } = t := by
  classical
  let zeros := List.replicate rts.length (HolWordLab.word (0 : BitVec width))
  let t' : CrepSemHOLState width σ := { t with locals := t.locals.updateListEq (rts.zip zeros) }
  have hnd := evalNestedDecsSeqResVarEqHOL
    (List.replicate rts.length (.const (0 : BitVec width))) rts t zeros
    (.seq (.call (some (rts, none)) fname cargs) B)
    ⟨by simp [zeros, evalCrepSemHOLExp], by simp, by
      simp [distinctListsHol, crepExpVarsHOL], hnodup⟩
  have hargs' : cargs.mapM (@evalCrepSemHOLExp width _ σ t'
      (fun address => Classical.propDecidable (t'.memaddrs address))) = some flat :=
    optMmapEvalDistinctListsNotAffectHOL cargs t flat rts zeros
      ⟨hargs, by simp [zeros], hdist⟩
  have hg : ∀ rts' h, (some (rts, none) : Option (List Nat × Option (BitVec width × CrepProgHOL width))) =
      some (rts', h) → rts'.Nodup := by
    intro rts' h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]; exact hnodup
  have hcall := crepCallTimeout t' (some (rts, none)) fname cargs flat body locals hargs'
    hlookup hg hclock
  rw [evalCrepSemHOLProgExact_seq_holShape, hcall] at hnd
  exact ⟨_, hnd, rfl⟩

private theorem mapM_congr_mem' {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x, x ∈ xs → f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.mapM_cons, h x (by simp),
        mapM_congr_mem' f g xs (fun y hy => h y (by simp [hy]))]

theorem decCallCtxt_lookup_ne {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (rt : MlS) (shape : ShapeHOL) (k : MlS) (hk : k ≠ rt) :
    (decCallCtxt ctxt rt shape).vars.lookup k = ctxt.vars.lookup k := by
  simp only [HolFiniteMapExact.lookup_update, FUPDATE]
  split
  · rename_i h; exact absurd (by simpa using h : rt = k).symm hk
  · rfl

theorem decCallCtxt_lookup_eq {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (rt : MlS) (shape : ShapeHOL) :
    (decCallCtxt ctxt rt shape).vars.lookup rt = some (shape, decCallSlots ctxt shape) := by
  simp [HolFiniteMapExact.lookup_update, FUPDATE]

/-- The caller's `locals_rel` after the DecCall continuation: the source
    restores `rt` with `res_var`, the target restores the fresh slots with the
    `nested_decs` fold. Slots of `rt` in the caller context must be unchanged by
    the continuation (HOL uses `unassigned_free_vars_evaluate_same` and
    `not_mem_context_assigned_mem_gt` for this). -/
theorem decCallLocalsRestore {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (rt : MlS) (shape : ShapeHOL)
    (sl : HolFiniteMapExact MlS (ValueHOL width)) (tl : HolFiniteMapExact Nat (HolWordLab width))
    (s2l : HolFiniteMapExact MlS (ValueHOL width)) (t2l : HolFiniteMapExact Nat (HolWordLab width))
    (hlocals : panToCrepLocalsRelFiniteExact ctxt sl tl)
    (hrel2 : panToCrepLocalsRelFiniteExact (decCallCtxt ctxt rt shape) s2l t2l)
    (hsame : ∀ sh ns x, ctxt.vars.lookup rt = some (sh, ns) → x ∈ ns →
      t2l.lookup x = tl.lookup x) :
    panToCrepLocalsRelFiniteExact ctxt (HolFiniteMapExact.resVarEq s2l (rt, sl.lookup rt))
      (((decCallSlots ctxt shape).zip ((decCallSlots ctxt shape).map tl.lookup)).foldl
        (fun current entry => HolFiniteMapExact.resVarEq current entry) t2l) := by
  refine ⟨hlocals.1, hlocals.2.1, ?_⟩
  have hfold : ∀ x, x ≤ ctxt.vmax →
      (((decCallSlots ctxt shape).zip ((decCallSlots ctxt shape).map tl.lookup)).foldl
        (fun current entry => HolFiniteMapExact.resVarEq current entry) t2l).lookup x =
        t2l.lookup x := by
    intro x hx
    exact flookupResVarDistinctZipEqHOL _ _ t2l x
      ⟨by simp, fun hm => by have := (decCallSlots_gt ctxt shape x hm).1; omega⟩
  intro k w hk
  rw [flookupPanResVarThmHOL] at hk
  split at hk
  · rename_i hkrt
    subst hkrt
    obtain ⟨slots, words, hv, hmm, hfl, hwf⟩ := hlocals.2.2 k w hk
    refine ⟨slots, words, hv, ?_, hfl, hwf⟩
    rw [← hmm]
    apply mapM_congr_mem'
    intro x hx
    rw [hfold x (hlocals.2.1.2 k _ slots hv x hx)]
    exact hsame _ slots x hv hx
  · rename_i hkrt
    obtain ⟨slots, words, hv, hmm, hfl, hwf⟩ := hrel2.2.2 k w hk
    rw [decCallCtxt_lookup_ne ctxt rt shape k hkrt] at hv
    refine ⟨slots, words, hv, ?_, hfl, hwf⟩
    rw [← hmm]
    apply mapM_congr_mem'
    intro x hx
    exact hfold x (hlocals.2.1.2 k _ slots hv x hx)

private theorem fupdateListHOL_zip_not_mem' {β : Type} (k : Nat) :
    ∀ (xs : List Nat) (ys : List β) (f : FiniteMap Nat β), k ∉ xs →
      FUPDATE_LIST_HOL f (xs.zip ys) k = f k
  | [], _, f, _ => by simp [FUPDATE_LIST_HOL]
  | _ :: _, [], f, _ => by simp [FUPDATE_LIST_HOL]
  | x :: xs, y :: ys, f, hk => by
      simp only [List.mem_cons, not_or] at hk
      rw [List.zip_cons_cons, FUPDATE_LIST_HOL_cons, fupdateListHOL_zip_not_mem' k xs ys _ hk.2]
      simp [FUPDATE_HOL, hk.1]

private theorem lookup_updateListEq_zip_not_mem {β : Type}
    (m : HolFiniteMapExact Nat β) (xs : List Nat) (ys : List β) (k : Nat) (hk : k ∉ xs) :
    (m.updateListEq (xs.zip ys)).lookup k = m.lookup k := by
  rw [HolFiniteMapExact.lookup_updateListEq]
  exact fupdateListHOL_zip_not_mem' k xs ys _ hk

/-- The two induction hypotheses of the `DecCall rt shape fname argexps prog1`
    case of HOL `panSem$evaluate_ind`, as rebound at `panSemScript.sml:777-778`,
    instantiated at `pcCompileCorrectAt`: the continuation IH at
    `set_var rt retv (st with locals := s.locals)` after the callee returns a
    value of both shapes, and the callee IH at `dec_clock s with locals :=
    newlocals`. -/
def pcCompileCorrectDecCallIH {width : Nat} {σ : Type} [NeZero width]
    (rt : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL width))
    (prog1 : ProgHOL width) (source : PanSemStateFiniteExact width σ) : Prop :=
  (∀ (values : List (ValueHOL width)) (prog : ProgHOL width)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
      (st : PanSemStateFiniteExact width σ) (retv : ValueHOL width),
    source.evalListHOLFinite
        (h := fun address => Classical.propDecidable (source.memaddrs address))
        arguments = some values →
    PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function values =
      some (prog, newlocals, returnShape) →
    source.clock ≠ 0 →
    (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals).evaluateHOLFiniteState
        prog = (some (.returned retv), st) →
    shapeOfHOLExact retv = shape →
    shapeOfHOLExact retv = returnShape →
    pcCompileCorrectAt prog1
      (PanSemStateFiniteExact.setVarHOLFinite rt retv { st with locals := source.locals })) ∧
  (∀ (values : List (ValueHOL width)) (prog : ProgHOL width)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
    source.evalListHOLFinite
        (h := fun address => Classical.propDecidable (source.memaddrs address))
        arguments = some values →
    PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function values =
      some (prog, newlocals, returnShape) →
    source.clock ≠ 0 →
    pcCompileCorrectAt prog (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals))

/-- HOL `pc_compile_correct[DecCall]` (`pan_to_crepProofScript.sml:4233-4485`)
    against `pcCompileCorrectAt`, from the DecCall IHs of the rebound
    `evaluate_ind`. Zero clock: both sides time out. The callee's TimeOut,
    FinalFFI, and Exception propagate with `empty_locals`. A Return of the right
    shapes runs the continuation IH at the extended context. Afterwards the
    source `res_var` and the target `nested_decs` restoration re-establish the
    caller's `locals_rel`. Every other outcome is a source Error, excluded by
    `res ≠ SOME Error`. No target run is assumed. Untagged: the tagged HOL-shaped
    statement is `pcCompileCorrect_DecCall`. -/
theorem pcCompileCorrectAt_decCall {width : Nat} {σ : Type} [NeZero width]
    (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
    (prog1 : ProgHOL width) (source : PanSemStateFiniteExact width σ)
    (ih : pcCompileCorrectDecCallIH rt shape fname argexps prog1 source) :
    pcCompileCorrectAt (.decCall rt shape fname argexps prog1 : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocAll : everyExpListHOL localisedExpHOL argexps = true ∧ localisedProgHOL prog1 = true := by
    simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  cases hargs : source.evalListHOLFinite
      (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps with
  | none =>
      rw [hargs] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some values =>
  rw [hargs] at hrun
  dsimp only at hrun
  cases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname values with
  | none =>
      rw [hlk] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some triple =>
  obtain ⟨prog, newlocals, rsh⟩ := triple
  rw [hlk] at hrun
  dsimp only at hrun
  obtain ⟨vshapes, _hsrc, hprogLoc, _hfuncs, _hlen, htargs, htlookup, hst', hcode',
    hexcp', hloc'⟩ :=
    pcCompileCorrectCallPrelude source t ctxt fname argexps values prog newlocals rsh
      hargs hlk hstate hcode hexcp hlocals hlocAll.1
  have hnodup := decCallSlots_nodup ctxt shape
  have hdist := pcCompileCorrectCallRetSlotsDistinct ctxt argexps (sizeOfShapeHOL shape)
    hlocals.2.1
  rw [compileDecCallShape]
  by_cases hclock : source.clock = 0
  · rw [if_pos hclock] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    have htclock : t.clock = 0 := by rw [← hstate.2.2.2.2.2.1]; exact hclock
    obtain ⟨t2, hrun2, hsame⟩ := crepNestedDecCallTimeout t fname _ _ _ _ _
      (compileProgExactHOLW (decCallCtxt ctxt rt shape) prog1) htargs htlookup htclock hnodup hdist
    refine ⟨_, t2, hrun2,
      panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals source t t2 hsame hstate,
      ?_, hexcp, rfl⟩
    have hcode2 : t2.code = t.code := by rw [← hsame]
    rw [hcode2]; exact hcode
  rw [if_neg hclock] at hrun
  have htclock : t.clock ≠ 0 := by rw [← hstate.2.2.2.2.2.1]; exact hclock
  rw [crepNestedDecCallTarget t fname _ _ _ _ _ _ htargs htlookup htclock hnodup hdist]
  rcases hbody : (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
      ).evaluateHOLFiniteState prog with ⟨bres, st⟩
  rw [hbody] at hrun
  dsimp only at hrun
  have herr : ∀ r1 : Option (CrepResultHOLExact width), bres = none ∨ bres = some .break ∨
      bres = some .continue ∨ bres = some .error → False := by
    intro _ hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact absurd (Prod.mk.inj hrun).1.symm hres
  obtain ⟨res1, t1, hrun1, hs, hc, he, hrr⟩ :=
    ih.2 values prog newlocals rsh hargs hlk hclock bres st _ _ hbody
      (fun h => herr none (Or.inr (Or.inr (Or.inr h)))) hst' hcode' hexcp' hloc' hprogLoc
  rw [hrun1]
  rcases bres with _ | r
  · exact (herr none (Or.inl rfl)).elim
  cases r with
  | error => exact (herr none (Or.inr (Or.inr (Or.inr rfl)))).elim
  | «break» => exact (herr none (Or.inr (Or.inl rfl))).elim
  | «continue» => exact (herr none (Or.inr (Or.inr (Or.inl rfl)))).elim
  | timeOut =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      simp only [pcCompileCorrectResultRel] at hrr
      subst hrr
      refine ⟨_, _, rfl, ?_, codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc, he, rfl⟩
      exact panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals st t1 _ rfl hs
  | finalFfi ev =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      simp only [pcCompileCorrectResultRel] at hrr
      subst hrr
      refine ⟨_, _, rfl, ?_, codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc, he, rfl⟩
      exact panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals st t1 _ rfl hs
  | exception eid exn =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      simp only [pcCompileCorrectResultRel] at hrr
      split at hrr
      · exact hrr.elim
      rename_i n hn
      obtain ⟨rfl, hglob⟩ := hrr
      refine ⟨_, _, rfl, ?_, codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc, he, ?_⟩
      · exact panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals st t1 _ rfl hs
      · simp only [pcCompileCorrectResultRel]
        rw [show ctxt.eids.lookup eid = some n from hn]
        exact ⟨rfl, by simpa [globalsLookupHOL, CrepSemHOLState.emptyLocals] using hglob⟩
  | returned retv =>
      dsimp only at hrun
      by_cases hsh : (shapeEqHOL (shapeOfHOLExact retv) shape &&
          shapeEqHOL (shapeOfHOLExact retv) rsh) = true
      case neg =>
        rw [if_neg hsh] at hrun
        exact absurd (Prod.mk.inj hrun).1.symm hres
      rw [if_pos hsh] at hrun
      simp only [Bool.and_eq_true] at hsh
      have h1 : shapeOfHOLExact retv = shape := (shapeEqHOL_eq_true _ _).mp hsh.1
      have h2 : shapeOfHOLExact retv = rsh := (shapeEqHOL_eq_true _ _).mp hsh.2
      simp only [pcCompileCorrectResultRel] at hrr
      subst hrr
      have hwfv : isWfShapeValueHOLExact [] retv = true := by
        have := panToCrepFiniteEvaluateShapeInvariantRetInst2 argexps source fname values prog
          newlocals rsh prog (.returned retv) st t ctxt t.locals
          (by simpa [evalListHOLFiniteClassical] using hargs)
          (PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hlk) hbody hstate hlocals
        simpa using this
      have hwf : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact retv) = true := by
        rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl retv]
        exact hwfv
      have hflen : (flattenHOL retv).length = sizeOfShapeHOL (shapeOfHOLExact retv) :=
        flattenHOL_length_eq_sizeOfShapeHOL retv hwf
      have hlenS : (flattenHOL retv).length = (decCallSlots ctxt shape).length := by
        simp [decCallSlots, hflen, h1]
      have hzlen : (decCallSlots ctxt shape).length =
          (List.replicate (decCallSlots ctxt shape).length
            (HolWordLab.word (0 : BitVec width))).length := by simp
      have hcallres : crepCallAfterBody
          { t with locals := t.locals.updateListEq ((decCallSlots ctxt shape).zip
              (List.replicate (decCallSlots ctxt shape).length (HolWordLab.word (0 : BitVec width)))) }
          (some (decCallSlots ctxt shape, none)) (some (.return (flattenHOL retv)), t1) =
          (none, { t1 with locals :=
            t.locals.updateListEq ((decCallSlots ctxt shape).zip (flattenHOL retv)) }) := by
        simp only [crepCallAfterBody]
        rw [if_neg (by rw [hlenS]; exact fun h => h rfl)]
        rw [mapM_lookup_updateListEq _ _ _ hnodup hzlen]
        dsimp only
        rw [updateListEq_overwrite t.locals _ _ _ hzlen hlenS.symm]
      rw [hcallres]
      dsimp only
      rw [if_pos rfl]
      rcases hcont : (PanSemStateFiniteExact.setVarHOLFinite rt retv
          { st with locals := source.locals }).evaluateHOLFiniteState prog1 with ⟨res2, s2⟩
      rw [hcont] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      have hlocc := localsRelExtendNewVarHOL ctxt source.locals t.locals retv rt
        (decCallSlots ctxt shape)
        ⟨hlocals, hwf, hnodup, fun y hy => by
          have := decCallSlots_gt ctxt shape y hy; rw [h1]; exact this,
          by rw [← hlenS, hflen]⟩
      rw [h1] at hlocc
      obtain ⟨res2', t2, hrun2, hs2, hc2, he2, hrr2⟩ :=
        ih.1 values prog newlocals rsh st retv hargs hlk hclock hbody h1 h2 res2 s2
          { t1 with locals := t.locals.updateListEq ((decCallSlots ctxt shape).zip (flattenHOL retv)) }
          (decCallCtxt ctxt rt shape) hcont hres
          (by simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.setVarHOLFinite] using hs)
          (codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc) he hlocc hlocAll.2
      rw [hrun2]
      have hsame : res2' = none ∨ res2' = some (.continue 0) ∨ res2' = some (.break 0) →
          ∀ sh ns x, ctxt.vars.lookup rt = some (sh, ns) → x ∈ ns →
            t2.locals.lookup x = t.locals.lookup x := by
        intro hform sh ns x hv hx
        have hxle : x ≤ ctxt.vmax := hlocals.2.1.2 rt sh ns hv x hx
        have hxnot : x ∉ decCallSlots ctxt shape := fun hm => by
          have := (decCallSlots_gt ctxt shape x hm).1; omega
        have hnot := notMemContextAssignedMemGtHOL (decCallCtxt ctxt rt shape) prog1 x
          ⟨hlocc.2.1, fun v sh' ns' hv' hx' => by
            by_cases hvrt : v = rt
            · subst hvrt
              rw [decCallCtxt_lookup_eq] at hv'
              simp only [Option.some.injEq, Prod.mk.injEq] at hv'
              rw [← hv'.2] at hx'
              exact hxnot hx'
            · rw [decCallCtxt_lookup_ne ctxt rt shape v hvrt] at hv'
              exact hvrt (hlocals.1.2 v rt sh' sh ns' ns hv' hv ⟨x, hx', hx⟩),
            Nat.le_trans hxle (Nat.le_add_right _ _)⟩
        have := crepUnassignedFreeVarsEvaluateSameHOL _ _ res2' t2 x 0 ⟨hrun2, hform, hnot⟩
        rw [this]
        exact lookup_updateListEq_zip_not_mem t.locals _ _ x hxnot
      refine ⟨res2', _, rfl, ?_, hc2, he2, ?_⟩
      · simpa [panToCrepStateRelFiniteExact] using hs2
      rcases res2 with _ | r2
      · obtain ⟨rfl, hl2⟩ := hrr2
        exact ⟨rfl, decCallLocalsRestore ctxt rt shape source.locals t.locals _ _ hlocals hl2
          (hsame (Or.inl rfl))⟩
      cases r2 with
      | error => exact hrr2.elim
      | «break» =>
          obtain ⟨rfl, hl2⟩ := hrr2
          exact ⟨rfl, decCallLocalsRestore ctxt rt shape source.locals t.locals _ _ hlocals hl2
            (hsame (Or.inr (Or.inr rfl)))⟩
      | «continue» =>
          obtain ⟨rfl, hl2⟩ := hrr2
          exact ⟨rfl, decCallLocalsRestore ctxt rt shape source.locals t.locals _ _ hlocals hl2
            (hsame (Or.inr (Or.inl rfl)))⟩
      | timeOut => exact hrr2
      | returned v => exact hrr2
      | finalFfi f => exact hrr2
      | exception eid v =>
          simp only [pcCompileCorrectResultRel] at hrr2 ⊢
          split at hrr2
          · exact hrr2.elim
          rename_i n hn
          exact ⟨hrr2.1, fun hsize => by simpa [globalsLookupHOL] using hrr2.2 hsize⟩

namespace PcCompileCorrectDecCallWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged DecCall case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectDecCallWitnesses

/-- HOL `pc_compile_correct`, `DecCall` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:4233`).
    This is the `DecCall rt shape fname argexps prog1` conjunct of the rebound
    `evaluate_ind` (`panSemScript.sml:777-778`) instantiated at HOL's induction
    predicate `P` (`pcCompileCorrectAtHOL`, whose body is exactly the unfolded
    conclusion below).

    The two IHs are transcribed binder for binder from HOL's printed
    `evaluate_ind` DecCall conjunct, including the TFL equation binders
    `v2 v7 eval_prog v v3` and the side conditions, in HOL order: the
    continuation IH (`shape_of retv = shape ∧ shape_of retv = return_sh ⇒
    P (prog1, set_var rt retv (st with locals := s.locals))`) and the callee IH
    (`P (prog, dec_clock s with locals := newlocals)`). The conclusion is
    `P (DecCall rt shape fname argexps prog1, s)` with HOL's conjunctive premise
    and inline `case res of`.

    Translation: as for `pcCompileCorrect_Call`. `evaluate` is the tagged
    total `evaluateHOLFiniteState` (line-780 `evaluate_def`) or
    `evalCrepSemHOLProgExact` (line-443 `evaluate_def`). `OPT_MMAP (eval s)` is
    the evaluator's classical-decision list step. `lookup_code`/`set_var`/
    `dec_clock` are the helpers the tagged Pan DecCall arm uses. The relations,
    `compile`, `globals_lookup`, `flatten`, `size_of_shape`, `shape_of`, and
    `localised_prog` are the tagged exact ports. The finite-map fields are the
    canonical `HolFiniteMapExact` translation of the listed carriers, and
    `'a word` is `BitVec width`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_DecCall {width : Nat} {σ : Type} [NeZero width] :
    ∀ (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
      (prog1 : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      (∀ (args : List (ValueHOL width))
          (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
          (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
          (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL)
          (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
          (v : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
          (v3 : PanSemResultExact width) (retv : ValueHOL width),
          s.evalListHOLFinite
              (h := fun address => Classical.propDecidable (s.memaddrs address))
              argexps = some args ∧
            PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v2 ∧
            v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ s.clock ≠ 0 ∧
            eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
              { s.decClockHOLFinite with locals := newlocals } prog ∧
            eval_prog = (v, st) ∧ v = some v3 ∧ v3 = .returned retv ∧
            shapeOfHOLExact retv = shape ∧ shapeOfHOLExact retv = return_sh →
          pcCompileCorrectAtHOL prog1
            (PanSemStateFiniteExact.setVarHOLFinite rt retv { st with locals := s.locals })) ∧
      (∀ (args : List (ValueHOL width))
          (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
          (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
          (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
          s.evalListHOLFinite
              (h := fun address => Classical.propDecidable (s.memaddrs address))
              argexps = some args ∧
            PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v2 ∧
            v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
          pcCompileCorrectAtHOL prog { s.decClockHOLFinite with locals := newlocals }) →
      ∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
        (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width),
        s.evaluateHOLFiniteState (.decCall rt shape fname argexps prog1) = (res, s1) ∧
          res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
          codeRelExactHOLW ctxt s.code t.code ∧
          panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
          panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
          localisedProgHOL (.decCall rt shape fname argexps prog1) = true →
        ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
          evalCrepSemHOLProgExact t
              (compileProgExactHOLW ctxt (.decCall rt shape fname argexps prog1)) =
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
  intro rt shape fname argexps prog1 s ⟨ihCont, ihBody⟩ res s1 t ctxt
    ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  have ih : pcCompileCorrectDecCallIH rt shape fname argexps prog1 s := by
    refine ⟨?_, ?_⟩
    · intro values prog newlocals returnShape st retv hargs hlk hclock hbody h1 h2
      exact (pcCompileCorrectAt_iff_HOL _ _).mpr <| ihCont values (prog, newlocals, returnShape)
        prog (newlocals, returnShape) newlocals returnShape (some (.returned retv), st)
        (some (.returned retv)) st (.returned retv) retv
        ⟨hargs, hlk, rfl, rfl, hclock, hbody.symm, rfl, rfl, rfl, h1, h2⟩
    · intro values prog newlocals returnShape hargs hlk hclock
      exact (pcCompileCorrectAt_iff_HOL _ _).mpr <| ihBody values (prog, newlocals, returnShape)
        prog (newlocals, returnShape) newlocals returnShape ⟨hargs, hlk, rfl, rfl, hclock⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_decCall rt shape fname argexps prog1 s ih res s1 t ctxt hrun hres hstate
      hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
