module

public import Flapjack.Pancake.Proofs.PanSimp.RetToTailCorrect
public import Flapjack.Pancake.Proofs.PanSimp.SeqAssocAssembly
public import Flapjack.Pancake.Semantics.PanSem.EvaluateInd

@[expose] public section

/-!
The recursive cases and the assembly of the original `ret_to_tail_correct`
(pan_simpProofScript.sml:182-341), with its helper lemmas
`evaluate_seq_call_ret_eq` (137), `evaluate_seq_no_error_fst` (153) and
`evaluate_while_no_error_imp` (103).
-/

namespace Flapjack.PanSimp.RetToTailCorrect

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

namespace RetToTailAssemblySupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end RetToTailAssemblySupport

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_no_error_fst"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqNoErrorFstHOL {width : Nat} {σ : Type} [NeZero width]
    (p p' : ProgHOL width) (s : PanSemStateFiniteExact width σ) :
    (evaluateHOLFiniteState s (.seq p p')).1 ≠ some .error →
      (evaluateHOLFiniteState s p).1 ≠ some .error := by
  rw [evaluateHOLFiniteState_seq_line780]
  intro h he
  apply h
  simp only [he]

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_call_ret_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqCallRetEqHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      (evaluateHOLFiniteState s p).1 ≠ some .error →
      evaluateHOLFiniteState s (seqCallRetHOL p) = evaluateHOLFiniteState s p := by
  intro p s h
  unfold seqCallRetHOL
  split
  · rename_i returnName function arguments returnedName
    split
    · rename_i heq
      subst heq
      revert h
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call,
        evaluateHOLFiniteState_call]
      dsimp only
      cases hargs : evalListHOLFinite s
          (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
      | none => intro _; rfl
      | some values =>
      dsimp only
      cases hl : lookupCodeHOLFinite s.code.lookup function values with
      | none => intro _; rfl
      | some entry =>
      obtain ⟨body, callee, returnShape⟩ := entry
      dsimp only
      by_cases hc : s.clock = 0
      · simp only [hc, ↓reduceIte]; intro _; trivial
      simp only [hc, ↓reduceIte]
      cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
      | mk res st =>
      rcases res with _ | r
      · intro _; rfl
      cases r with
      | returned v =>
        dsimp only
        by_cases hsh : shapeEqHOL (shapeOfHOLExact v) returnShape = true
        · by_cases hv : isValidValueHOLExact s.toExact .local returnName v = true
          · simp only [hsh, hv, ↓reduceIte, evaluateHOLFiniteState_return]
            simp only [setKvarHOLFinite, setVarHOLFinite]
            split
            · rename_i hnone
              change (s.locals.update (returnName, v)).lookup returnName = none at hnone
              simp [FUPDATE] at hnone
            · rename_i value hsome
              change (s.locals.update (returnName, v)).lookup returnName = some value at hsome
              have hvv : value = v := by simp [FUPDATE] at hsome; exact hsome.symm
              subst hvv
              by_cases hsz : sizeOfShapeWithContextHOL st.structs (shapeOfHOLExact value) ≤ 32
              · simp only [hsz, ↓reduceIte]; intro _; rfl
              · simp only [hsz, ↓reduceIte]; intro h; exact absurd rfl h
          · simp only [hsh, hv, ↓reduceIte]; intro h; exact absurd rfl h
        · simp only [hsh]; intro _; rfl
      | _ => intro _; rfl
    · rfl
  · rfl

private def retToTailCorrectP {width : Nat} {σ : Type} [NeZero width]
    (x : ProgHOL width × PanSemStateFiniteExact width σ) : Prop :=
  (evaluateHOLFiniteState x.2 x.1).1 ≠ some .error →
    evaluateHOLFiniteState x.2 (retToTailHOL x.1) = evaluateHOLFiniteState x.2 x.1

/-- Resume `ret_to_tail_correct[Seq]`. -/
private theorem retToTailCorrect_seq {width : Nat} {σ : Type} [NeZero width]
    (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (ih : (∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
        (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s c1 ∧ res = none →
        retToTailCorrectP (width := width) (σ := σ) (c2, s1)) ∧
      retToTailCorrectP (width := width) (σ := σ) (c1, s))
    (h : (evaluateHOLFiniteState s (.seq c1 c2)).1 ≠ some .error) :
    evaluateHOLFiniteState s (retToTailHOL (.seq c1 c2)) =
      evaluateHOLFiniteState s (.seq c1 c2) := by
  dsimp only [retToTailCorrectP] at *
  have hseq : evaluateHOLFiniteState s (.seq (retToTailHOL c1) (retToTailHOL c2)) =
      evaluateHOLFiniteState s (.seq c1 c2) := by
    have h1 := evaluateSeqNoErrorFstHOL c1 c2 s h
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780, ih.2 h1]
    rw [evaluateHOLFiniteState_seq_line780] at h
    cases hr : evaluateHOLFiniteState s c1 with
    | mk r s1 =>
      rw [hr] at h
      cases r with
      | none =>
        dsimp only at h ⊢
        exact ih.1 none s1 ⟨hr.symm, rfl⟩ h
      | some _ => rfl
  rw [retToTailHOL.eq_3, evaluateSeqCallRetEqHOL _ s (by rw [hseq]; exact h), hseq]

/-- Resume `ret_to_tail_correct[If]`. -/
private theorem retToTailCorrect_if {width : Nat} {σ : Type} [NeZero width]
    (e : ExpHOL width) (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (ih : ∀ (v1 : ValueHOL width) (v6 : HolWordLab width) (w : BitVec width),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v1 ∧
        v1 = .val v6 ∧ v6 = .word w →
      retToTailCorrectP (width := width) (σ := σ) (if w ≠ 0 then c1 else c2, s))
    (h : (evaluateHOLFiniteState s (.ite e c1 c2)).1 ≠ some .error) :
    evaluateHOLFiniteState s (retToTailHOL (.ite e c1 c2)) =
      evaluateHOLFiniteState s (.ite e c1 c2) := by
  dsimp only [retToTailCorrectP] at *
  rw [retToTailHOL.eq_4, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_ite]
  rw [evaluateHOLFiniteState_ite] at h
  cases hev : @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) e with
  | none => rfl
  | some v =>
    rw [hev] at h
    cases v with
    | val x =>
      cases x with
      | word w =>
        have hb := ih _ _ w ⟨hev, rfl, rfl⟩
        dsimp only at h hb ⊢
        by_cases hw : w = 0
        · rw [if_pos hw] at h
          rw [if_pos hw, if_pos hw]
          rw [if_neg (fun h' => h' hw)] at hb
          exact hb h
        · rw [if_neg hw] at h
          rw [if_neg hw, if_neg hw]
          rw [if_pos hw] at hb
          exact hb h
    | _ => rfl

/-- Resume `ret_to_tail_correct[While]`. -/
private theorem retToTailCorrect_while {width : Nat} {σ : Type} [NeZero width]
    (e : ExpHOL width) (c : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (ih : (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
          (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
          (v1 : PanSemResultExact width),
        @evalHOLExact width σ _ s.toExact
            (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
          v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
          (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
          res = some v1 ∧ v1 = .continue →
        retToTailCorrectP (width := width) (σ := σ) (.while e c, s1)) ∧
      (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
          (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
        @evalHOLExact width σ _ s.toExact
            (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
          v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
          (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
          res = none →
        retToTailCorrectP (width := width) (σ := σ) (.while e c, s1)) ∧
      (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
        @evalHOLExact width σ _ s.toExact
            (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
          v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 →
        retToTailCorrectP (width := width) (σ := σ) (c, s.decClockHOLFinite)))
    (h : (evaluateHOLFiniteState s (.while e c)).1 ≠ some .error) :
    evaluateHOLFiniteState s (retToTailHOL (.while e c)) =
      evaluateHOLFiniteState s (.while e c) := by
  dsimp only [retToTailCorrectP] at *
  rw [retToTailHOL.eq_5]
  rw [evaluateHOLFiniteState_while_fixClockRewrite s e (retToTailHOL c),
    evaluateHOLFiniteState_while_fixClockRewrite s e c]
  rw [evaluateHOLFiniteState_while_fixClockRewrite s e c] at h
  rw [evalHOLFinite] at h ⊢
  cases hev : @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) e with
  | none => rfl
  | some v =>
    rw [hev] at h
    cases v with
    | val x =>
      cases x with
      | word w =>
        dsimp only at h ⊢
        by_cases hw : w ≠ 0
        · rw [if_pos hw] at h
          rw [if_pos hw, if_pos hw]
          by_cases hc : s.clock = 0
          · rw [if_pos hc, if_pos hc]
          rw [if_neg hc] at h
          rw [if_neg hc, if_neg hc]
          have hbIH := ih.2.2 _ _ w ⟨hev, rfl, rfl, hw, hc⟩
          cases hb : evaluateHOLFiniteState (decClockHOLFinite s) c with
          | mk r s1 =>
            rw [hb] at h hbIH
            have hne : r ≠ some .error := by
              intro hr; subst hr; exact h rfl
            rw [hbIH hne]
            dsimp only at h ⊢
            rcases r with _ | r
            · have := ih.2.1 _ _ w none s1 ⟨hev, rfl, rfl, hw, hc, hb.symm, rfl⟩
              rw [retToTailHOL.eq_5] at this
              exact this h
            · cases r with
              | «continue» =>
                have := ih.1 _ _ w (some .continue) s1 .continue
                  ⟨hev, rfl, rfl, hw, hc, hb.symm, rfl, rfl⟩
                rw [retToTailHOL.eq_5] at this
                exact this h
              | _ => rfl
        · rw [if_neg hw, if_neg hw]
    | _ => rfl

private def retToTailCorrectCallIH {width : Nat} {σ : Type} [NeZero width]
    (caltyp : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (argexps : List (ExpHOL width))
    (s : PanSemStateFiniteExact width σ) : Prop :=
  (∀ (args : List (ValueHOL width))
      (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
      (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL)
      (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
      (v4 : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
      (v8 : PanSemResultExact width) (eid : MlS) (exn : ValueHOL width)
      (v : Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))
      (v1 : Option (VarKind × MlS)) (v2 : Option (MlS × MlS × ProgHOL width))
      (v3 : MlS × MlS × ProgHOL width) (eid' : MlS) (v5 : MlS × ProgHOL width)
      (evar : MlS) (p : ProgHOL width) (sh : ShapeHOL),
    s.evalListHOLFinite
        (h := fun address => Classical.propDecidable (s.memaddrs address))
        argexps = some args ∧
      PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
      v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 ∧
      eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
        { s.decClockHOLFinite with locals := newlocals } prog ∧
      eval_prog = (v4, st) ∧ v4 = some v8 ∧ v8 = .exception eid exn ∧
      caltyp = some v ∧ v = (v1, v2) ∧ v2 = some v3 ∧ v3 = (eid', v5) ∧
      v5 = (evar, p) ∧ eid = eid' ∧ s.eshapes.lookup eid = some sh ∧
      shapeOfHOLExact exn = sh ∧ isValidValueHOLExact s.toExact .local evar exn = true →
    retToTailCorrectP (width := width) (σ := σ)
      (p, PanSemStateFiniteExact.setVarHOLFinite evar exn { st with locals := s.locals })) ∧
  (∀ (args : List (ValueHOL width))
      (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
      (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
    s.evalListHOLFinite
        (h := fun address => Classical.propDecidable (s.memaddrs address))
        argexps = some args ∧
      PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
      v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
    retToTailCorrectP (width := width) (σ := σ)
      (prog, { s.decClockHOLFinite with locals := newlocals }))

private def retToTailCorrectDecCallIH {width : Nat} {σ : Type} [NeZero width]
    (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
    (prog1 : ProgHOL width) (s : PanSemStateFiniteExact width σ) : Prop :=
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
    retToTailCorrectP (width := width) (σ := σ)
      (prog1, PanSemStateFiniteExact.setVarHOLFinite rt retv { st with locals := s.locals })) ∧
  (∀ (args : List (ValueHOL width))
      (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
      (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
    s.evalListHOLFinite
        (h := fun address => Classical.propDecidable (s.memaddrs address))
        argexps = some args ∧
      PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v2 ∧
      v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
    retToTailCorrectP (width := width) (σ := σ)
      (prog, { s.decClockHOLFinite with locals := newlocals }))

/-- Resume `ret_to_tail_correct[Call]`. -/
private theorem retToTailCorrect_call {width : Nat} {σ : Type} [NeZero width]
    (caltyp : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (argexps : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ)
    (ih : retToTailCorrectCallIH (width := width) (σ := σ) caltyp fname argexps s)
    (h : (evaluateHOLFiniteState s (.call caltyp fname argexps)).1 ≠ some .error) :
    evaluateHOLFiniteState s (retToTailHOL (.call caltyp fname argexps)) =
      evaluateHOLFiniteState s (.call caltyp fname argexps) := by
  dsimp only [retToTailCorrectCallIH, retToTailCorrectP] at *
  rcases caltyp with _ | ⟨returns, _ | ⟨eid, evar, hp⟩⟩
  · rw [retToTailHOL.eq_6]
  · rw [retToTailHOL.eq_7]
  rw [retToTailHOL.eq_8]
  revert h
  rw [evaluateHOLFiniteState_call s (some (returns, some (eid, evar, retToTailHOL hp))),
    evaluateHOLFiniteState_call s (some (returns, some (eid, evar, hp)))]
  cases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) argexps with
  | none => intro _; rfl
  | some values =>
  dsimp only
  cases hl : lookupCodeHOLFinite s.code.lookup fname values with
  | none => intro _; rfl
  | some entry =>
  obtain ⟨body, callee, returnShape⟩ := entry
  dsimp only
  by_cases hc : s.clock = 0
  · rw [if_pos hc, if_pos hc]; intro _; rfl
  rw [if_neg hc, if_neg hc]
  cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
  | mk res st =>
  rcases res with _ | r
  · intro _; rfl
  cases r with
  | exception exceptionId value =>
    dsimp only
    by_cases heid : exceptionId = eid
    · rw [if_pos heid, if_pos heid]
      cases hesh : s.eshapes.lookup exceptionId with
      | none => intro _; rfl
      | some shape =>
        dsimp only
        by_cases hcond : (shapeEqHOL (shapeOfHOLExact value) shape &&
            isValidValueHOLExact s.toExact .local evar value) = true
        · rw [if_pos hcond, if_pos hcond]
          intro h
          simp only [Bool.and_eq_true] at hcond
          exact ih.1 values (body, callee, returnShape) body (callee, returnShape) callee
            returnShape _ _ st _ exceptionId value _ returns _ _ eid _ evar hp shape
            ⟨hargs, hl, rfl, rfl, hc, hb.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, heid,
              hesh, (shapeEqHOL_eq_true _ _).mp hcond.1, hcond.2⟩ h
        · rw [if_neg hcond, if_neg hcond]; intro _; rfl
    · rw [if_neg heid, if_neg heid]; intro _; rfl
  | returned v => rcases returns with _ | ⟨k, n⟩ <;> intro _ <;> rfl
  | _ => intro _; rfl

/-- Resume `ret_to_tail_correct[DecCall]`. -/
private theorem retToTailCorrect_decCall {width : Nat} {σ : Type} [NeZero width]
    (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
    (prog1 : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (ih : retToTailCorrectDecCallIH (width := width) (σ := σ) rt shape fname argexps prog1 s)
    (h : (evaluateHOLFiniteState s (.decCall rt shape fname argexps prog1)).1 ≠ some .error) :
    evaluateHOLFiniteState s (retToTailHOL (.decCall rt shape fname argexps prog1)) =
      evaluateHOLFiniteState s (.decCall rt shape fname argexps prog1) := by
  dsimp only [retToTailCorrectDecCallIH, retToTailCorrectP] at *
  rw [retToTailHOL.eq_9]
  revert h
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite s rt shape fname argexps
      (retToTailHOL prog1),
    evaluateHOLFiniteState_decCall_fixClockRewrite s rt shape fname argexps prog1]
  cases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) argexps with
  | none => intro _; rfl
  | some values =>
  dsimp only
  cases hl : lookupCodeHOLFinite s.code.lookup fname values with
  | none => intro _; rfl
  | some entry =>
  obtain ⟨body, callee, returnShape⟩ := entry
  dsimp only
  by_cases hc : s.clock = 0
  · rw [if_pos hc, if_pos hc]; intro _; rfl
  rw [if_neg hc, if_neg hc]
  cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
  | mk res st =>
  dsimp only
  rcases res with _ | r
  · intro _; rfl
  cases r with
  | returned v =>
    dsimp only
    by_cases hcond : (shapeEqHOL (shapeOfHOLExact v) shape &&
        shapeEqHOL (shapeOfHOLExact v) returnShape) = true
    · rw [if_pos hcond, if_pos hcond]
      simp only [Bool.and_eq_true] at hcond
      intro h
      have hIH := ih.1 values (body, callee, returnShape) body (callee, returnShape) callee
        returnShape _ _ st _ v
        ⟨hargs, hl, rfl, rfl, hc, hb.symm, rfl, rfl, rfl,
          (shapeEqHOL_eq_true _ _).mp hcond.1, (shapeEqHOL_eq_true _ _).mp hcond.2⟩ h
      rw [hIH]
    · rw [if_neg hcond, if_neg hcond]; intro _; rfl
  | _ => intro _; rfl

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrectHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (prog : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      (evaluateHOLFiniteState s prog).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL prog) = evaluateHOLFiniteState s prog := by
  have key := evaluateIndHOL (σ := σ) (width := width)
    (retToTailCorrectP (width := width) (σ := σ))
  refine fun prog s => key ⟨fun s => retToTailCorrect_skip s,
    fun v sh e prog s ih => retToTailCorrect_dec s v sh e prog ih,
    fun vk v src s => retToTailCorrect_assign s vk v src,
    fun v pop es s => retToTailCorrect_primitive s v pop es,
    fun dst src s => retToTailCorrect_store s dst src,
    fun dst src s => retToTailCorrect_store32 s dst src,
    fun dst src s => retToTailCorrect_storeByte s dst src,
    fun op vk v ad s => retToTailCorrect_shMemLoad s op vk v ad,
    fun op ad e s => retToTailCorrect_shMemStore s op ad e,
    retToTailCorrect_seq, retToTailCorrect_if,
    fun s => retToTailCorrect_break s,
    fun s => retToTailCorrect_continue s,
    retToTailCorrect_while,
    fun e s => retToTailCorrect_return s e,
    fun eid e s => retToTailCorrect_raise s eid e,
    fun s => retToTailCorrect_tick s,
    fun v0 v1 s => retToTailCorrect_annot s v0 v1,
    retToTailCorrect_call, retToTailCorrect_decCall,
    fun i p1 l1 p2 l2 s => retToTailCorrect_extCall s i p1 l1 p2 l2⟩ prog s

end Flapjack.PanSimp.RetToTailCorrect
