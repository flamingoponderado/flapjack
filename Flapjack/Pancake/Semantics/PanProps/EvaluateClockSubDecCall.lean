import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubCall

/-!
# panProps `evaluate_clock_sub`: the `DecCall` case

`DecCall` case of HOL `evaluate_clock_sub`
(`cakeml/pancake/semantics/panPropsScript.sml:724-728`, bead
`flapjack-4ac.4.60.1.1.14`).  The canonical-carrier core `decCallCore` is
untagged support; the tagged case theorem states the pair-carrier case with
the two literal `evaluate_ind` DecCall premises (callee and continuation).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace EvaluateClockSubDecCall
open EvaluateClockSubAtoms EvaluateClockSubCall

set_option linter.unusedSimpArgs false in
theorem decCallCore {width : Nat} {σ : Type} [NeZero width]
    (rt : MlS) (shape : ShapeHOL) (f : MlS) (args : List (ExpHOL width))
    (prog1 : ProgHOL width) (u : PanSemStateFiniteExact width σ)
    (ihC : ∀ values prog nl rsh,
      evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args = some values →
      lookupCodeHOLFinite u.code.lookup f values = some (prog, nl, rsh) → u.clock ≠ 0 →
      Mc (callEntryStateHOLFinite u nl) prog)
    (ihK : ∀ values prog nl rsh st0 retv,
      evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args = some values →
      lookupCodeHOLFinite u.code.lookup f values = some (prog, nl, rsh) → u.clock ≠ 0 →
      evaluateHOLFiniteState (callEntryStateHOLFinite u nl) prog = (some (.returned retv), st0) →
      shapeOfHOLExact retv = shape → shapeOfHOLExact retv = rsh →
      Mc (setVarHOLFinite rt retv { st0 with locals := u.locals }) prog1) :
    Mc u (.decCall rt shape f args prog1) := by
  classical
  intro res st ck hHigh hnt
  apply clockSub_of_lowNoTimeout _ _ _ _ _ hHigh
  suffices hfst : (evaluateHOLFiniteState { u with clock := u.clock - ck }
      (.decCall rt shape f args prog1)).1 = res by
    rw [hfst]; exact hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hHigh ⊢
  rw [evalList_upd_clock]
  cases hargs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with
  | none => rw [hargs] at hHigh; simp only at hHigh ⊢; exact (Prod.mk.inj hHigh).1
  | some values =>
    rw [hargs] at hHigh
    simp only at hHigh ⊢
    cases hlk : lookupCodeHOLFinite u.code.lookup f values with
    | none => rw [hlk] at hHigh; simp only at hHigh ⊢; exact (Prod.mk.inj hHigh).1
    | some trip =>
      obtain ⟨prog, nl, rsh⟩ := trip
      rw [hlk] at hHigh
      simp only at hHigh ⊢
      by_cases hc0 : u.clock = 0
      · rw [if_pos hc0] at hHigh
        exact absurd (Prod.mk.inj hHigh).1.symm hnt
      rw [if_neg hc0] at hHigh
      rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite u nl) prog with ⟨r0, st0⟩
      rw [hb] at hHigh
      have hc0le := evaluateHOLFiniteState_clock_le_result _ _ _ _ hb
      simp only [callEntryStateHOLFinite] at hc0le
      have lowCallee : ck ≤ st0.clock → r0 ≠ some .timeOut →
          evaluateHOLFiniteState (callEntryStateHOLFinite { u with clock := u.clock - ck } nl) prog =
            (r0, { st0 with clock := st0.clock - ck }) := by
        intro hck hr0
        rw [callEntry_low]
        exact ihC values prog nl rsh hargs hlk hc0 r0 _ ck
          (by rw [hb]; exact congrArg (Prod.mk r0) (unshift st0 ck hck)) hr0
      have hlow0 : ck ≤ st0.clock → u.clock - ck ≠ 0 := by
        intro hck; omega
      rcases r0 with _ | ⟨_ | _ | _ | _ | v | ⟨e, v⟩ | ev⟩
      all_goals simp only at hHigh
      · obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only []
        exact hres
      · obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only []
        exact hres
      · exact absurd (Prod.mk.inj hHigh).1.symm hnt
      · obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only []
        exact hres
      · obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only []
        exact hres
      · by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape && shapeEqHOL (shapeOfHOLExact v) rsh) = true
        · simp only [hsh, if_true] at hHigh
          obtain ⟨hs1, hs2⟩ := Bool.and_eq_true_iff.mp hsh
          rcases hk : evaluateHOLFiniteState
              (setVarHOLFinite rt v { st0 with locals := u.locals }) prog1 with ⟨rk, stk⟩
          rw [hk] at hHigh
          simp only at hHigh
          obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
          have hkle := evaluateHOLFiniteState_clock_le_result _ _ _ _ hk
          simp only [setVarHOLFinite] at hkle
          have hstk : stk.clock = st.clock + ck := by
            have := congrArg PanSemStateFiniteExact.clock hst
            simpa using this
          have hck : ck ≤ st0.clock := by omega
          rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
          simp only [hsh, if_true]
          have hmc := ihK values prog nl rsh st0 v hargs hlk hc0 hb
            ((shapeEqHOL_eq_true _ _).mp hs1) ((shapeEqHOL_eq_true _ _).mp hs2) rk
            { stk with clock := stk.clock - ck } ck
            (by rw [hk]; exact congrArg (Prod.mk rk) (unshift stk ck (by omega)))
            (by rw [hres]; exact hnt)
          have hstate : setVarHOLFinite rt v
              { ({ st0 with clock := st0.clock - ck } : PanSemStateFiniteExact width σ) with
                locals := u.locals } =
              { setVarHOLFinite rt v { st0 with locals := u.locals } with
                clock := (setVarHOLFinite rt v { st0 with locals := u.locals }).clock - ck } := rfl
          rw [hstate, hmc]
          exact hres
        · simp only [hsh, if_false, Bool.false_eq_true] at hHigh
          obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
          have hck : ck ≤ st0.clock := by
            have := congrArg PanSemStateFiniteExact.clock hst
            simp only [emptyLocalsHOLFinite] at this
            omega
          rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
          simp only [hsh, if_false, Bool.false_eq_true]
          exact hres
      · obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only []
        exact hres
      · obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only []
        exact hres

end EvaluateClockSubDecCall

namespace EvaluateClockSubDecCallWitness
/-- Same-module canonical witness for the `locals`/`globals`/`code`/`eshapes`
    finite-map qualifier of the case theorem below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanPropsEvalStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
        PanPropsEvalStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanPropsEvalStateFiniteExact.holFmapAsFiniteSupportWitness
end EvaluateClockSubDecCallWitness

open EvaluateClockSubCall EvaluateClockSubDecCall

abbrev clockSubDecCallCalleeIH {width : Nat} {σ : Type}
    [NeZero width] (fname : MlS) (argexps : List (ExpHOL width))
    (s : PanPropsEvalStateFiniteExact width σ) : Prop :=
  ∀ (args : List (ValueHOL width))
    (v2 : ProgHOL width × (HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL))
    (prog : ProgHOL width)
    (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (return_sh : ShapeHOL),
    argexps.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite s.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (s.toPanSemFinite.memaddrs address)) expression) = some args →
    PanSemStateFiniteExact.lookupCodeHOLFinite s.toPanSemFinite.code.lookup
      fname args = some (v2.1, v2.2.1, v2.2.2) →
    v2 = (prog, v7) →
    v7 = (newlocals, return_sh) →
    s.toPanSemFinite.clock ≠ 0 →
    clockSubAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.callEntryStateHOLFinite s.toPanSemFinite newlocals)) prog

/-- HOL's DecCall continuation IH
    (`P (prog1, set_var rt retv (st with locals := s.locals))`) at
    `P = clockSubAtHOLFinite`, binder for binder. -/
abbrev clockSubDecCallContIH {width : Nat} {σ : Type}
    [NeZero width] (rt : MlS) (shape : ShapeHOL) (fname : MlS)
    (argexps : List (ExpHOL width)) (prog1 : ProgHOL width)
    (s : PanPropsEvalStateFiniteExact width σ) : Prop :=
  ∀ (args : List (ValueHOL width))
    (v2 : ProgHOL width × (HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL))
    (prog : ProgHOL width)
    (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (return_sh : ShapeHOL)
    (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (v : Option (PanSemResultExact width))
    (st : PanSemStateFiniteExact width σ)
    (v3 : PanSemResultExact width) (retv : ValueHOL width),
    argexps.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite s.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (s.toPanSemFinite.memaddrs address)) expression) = some args →
    PanSemStateFiniteExact.lookupCodeHOLFinite s.toPanSemFinite.code.lookup
      fname args = some (v2.1, v2.2.1, v2.2.2) →
    v2 = (prog, v7) →
    v7 = (newlocals, return_sh) →
    s.toPanSemFinite.clock ≠ 0 →
    eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.callEntryStateHOLFinite s.toPanSemFinite newlocals) prog →
    eval_prog = (v, st) →
    v = some v3 →
    v3 = .returned retv →
    shapeOfHOLExact retv = shape →
    shapeOfHOLExact retv = return_sh →
    clockSubAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.setVarHOLFinite rt retv
          { st with locals := s.toPanSemFinite.locals })) prog1

/-- `DecCall` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`),
    with exactly the two guarded `evaluate_ind` DecCall premises (continuation
    and callee) at the clock-sub motive, in the statement shape of the accepted
    cases.  The proof (`decCallCore`) shows that the clock-subtracted run cannot
    time out: the callee IH aligns the callee run, the continuation IH the
    continuation run, and `evaluate_clock` bounds `ck`.  `evaluate_add_clock_eq`
    then lifts the low run back to the given one. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubDecCallCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
    (prog1 : ProgHOL width) :
    ∀ (s : PanPropsEvalStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair s
          (.decCall rt shape fname argexps prog1 : ProgHOL width) =
        (res, { st with clock := st.clock + ck }) →
      res ≠ some .timeOut →
      clockSubDecCallContIH rt shape fname argexps prog1 s →
      clockSubDecCallCalleeIH fname argexps s →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { s with clock := s.clock - ck } (.decCall rt shape fname argexps prog1) =
          (res, st) := by
  classical
  intro s res st ck hRun hnt ihK ihC
  refine pair_of_mc s _ ?_ res st ck hRun hnt
  apply decCallCore
  · intro values prog nl rsh hargs hlk hc0
    apply mc_of_pair
    exact ihC values (prog, (nl, rsh)) prog (nl, rsh) nl rsh
      (by rw [← evalList_eq_mapM]; exact hargs) hlk rfl rfl hc0
  · intro values prog nl rsh st0 retv hargs hlk hc0 hb hsh hrsh
    apply mc_of_pair
    exact ihK values (prog, (nl, rsh)) prog (nl, rsh) nl rsh (some (.returned retv), st0)
      (some (.returned retv)) st0 (.returned retv) retv
      (by rw [← evalList_eq_mapM]; exact hargs) hlk rfl rfl hc0 hb.symm rfl rfl rfl hsh hrsh

end Flapjack
