import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubAtoms

/-!
# panProps `evaluate_clock_sub`: the `Call` case

`Call` case of HOL `evaluate_clock_sub` (`cakeml/pancake/semantics/panPropsScript.sml:724-728`,
bead `flapjack-4ac.4.60.1.1.13`).  The canonical-carrier core `callCore` is
untagged support; the tagged case theorem states the pair-carrier case with
the two literal `evaluate_ind` Call premises.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace EvaluateClockSubCall
open EvaluateClockSubAtoms

/-- The canonical-carrier `evaluate_clock_sub` motive. -/
def Mc {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateFiniteExact width σ) (p : ProgHOL width) : Prop :=
  ∀ (res : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ) (ck : Nat),
    evaluateHOLFiniteState u p = (res, { st with clock := st.clock + ck }) →
    res ≠ some .timeOut →
    evaluateHOLFiniteState { u with clock := u.clock - ck } p = (res, st)

theorem evalList_upd_clock {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateFiniteExact width σ) (c : Nat) (args : List (ExpHOL width)) :
    evalListHOLFinite { u with clock := c }
        (h := fun a => Classical.propDecidable (({ u with clock := c } :
          PanSemStateFiniteExact width σ).memaddrs a)) args =
      evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args := by
  classical
  simp only [evalListHOLFinite_eq_toExact]
  induction args with
  | nil => rfl
  | cons e rest ih =>
      simp only [evalListHOLExact]
      rw [ih]
      congr 1
      exact @evalHOLExact_upd_clock_eq width σ _ u.toExact _ e c

theorem isValid_upd_clock {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateFiniteExact width σ) (c : Nat) (k : VarKind) (n : MlS) (v : ValueHOL width) :
    isValidValueHOLExact ({ u with clock := c } : PanSemStateFiniteExact width σ).toExact k n v =
      isValidValueHOLExact u.toExact k n v := by
  cases k <;> rfl

theorem unshift {width : Nat} {σ : Type} [NeZero width]
    (x : PanSemStateFiniteExact width σ) (ck : Nat) (h : ck ≤ x.clock) :
    x = { ({ x with clock := x.clock - ck } : PanSemStateFiniteExact width σ) with
      clock := ({ x with clock := x.clock - ck } : PanSemStateFiniteExact width σ).clock + ck } := by
  cases x
  simp only at h
  simp only [PanSemStateFiniteExact.mk.injEq, and_true, true_and]
  omega

theorem callEntry_low {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateFiniteExact width σ) (ck : Nat) (nl : HolFiniteMapExact MlS (ValueHOL width)) :
    callEntryStateHOLFinite { u with clock := u.clock - ck } nl =
      { callEntryStateHOLFinite u nl with clock := (callEntryStateHOLFinite u nl).clock - ck } := by
  simp only [callEntryStateHOLFinite, PanSemStateFiniteExact.mk.injEq, and_true, true_and]
  omega

theorem setVar_upd_clock {width : Nat} {σ : Type} [NeZero width]
    (x : PanSemStateFiniteExact width σ) (c : Nat) (n : MlS) (v : ValueHOL width) :
    setVarHOLFinite n v { x with clock := c } = { setVarHOLFinite n v x with clock := c } := rfl

theorem setKvar_clock {width : Nat} {σ : Type} [NeZero width]
    (x : PanSemStateFiniteExact width σ) (k : VarKind) (n : MlS) (v : ValueHOL width) :
    (setKvarHOLFinite k n v x).clock = x.clock := by
  cases k <;> rfl

set_option linter.unusedSimpArgs false in
theorem callCore {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (f : MlS) (args : List (ExpHOL width)) (u : PanSemStateFiniteExact width σ)
    (ihC : ∀ values prog nl rsh,
      evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args = some values →
      lookupCodeHOLFinite u.code.lookup f values = some (prog, nl, rsh) → u.clock ≠ 0 →
      Mc (callEntryStateHOLFinite u nl) prog)
    (ihH : ∀ values prog nl rsh st0 eid exn v1 hid hv hp sh,
      evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args = some values →
      lookupCodeHOLFinite u.code.lookup f values = some (prog, nl, rsh) → u.clock ≠ 0 →
      evaluateHOLFiniteState (callEntryStateHOLFinite u nl) prog = (some (.exception eid exn), st0) →
      info = some (v1, some (hid, hv, hp)) → eid = hid →
      u.eshapes.lookup eid = some sh → shapeOfHOLExact exn = sh →
      isValidValueHOLExact u.toExact .local hv exn = true →
      Mc (setVarHOLFinite hv exn { st0 with locals := u.locals }) hp) :
    Mc u (.call info f args) := by
  classical
  intro res st ck hHigh hnt
  apply clockSub_of_lowNoTimeout _ _ _ _ _ hHigh
  suffices hfst : (evaluateHOLFiniteState { u with clock := u.clock - ck } (.call info f args)).1 = res by
    rw [hfst]; exact hnt
  rw [evaluateHOLFiniteState_call] at hHigh ⊢
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
      simp only [isValid_upd_clock]
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
      · simp only at hHigh
        obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite, setKvar_clock] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only
        exact hres
      · simp only at hHigh
        obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite, setKvar_clock] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only
        exact hres
      · simp only at hHigh
        exact absurd (Prod.mk.inj hHigh).1.symm hnt
      · simp only at hHigh
        obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite, setKvar_clock] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only
        exact hres
      · simp only at hHigh
        obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite, setKvar_clock] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only
        exact hres
      · by_cases hsh : shapeEqHOL (shapeOfHOLExact v) rsh = true
        · rcases info with _ | ⟨_ | ⟨k, n⟩, x⟩
          · simp only [hsh, if_true] at hHigh
            obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
            have hck : ck ≤ st0.clock := by
              have := congrArg PanSemStateFiniteExact.clock hst
              simp only [emptyLocalsHOLFinite, setKvar_clock] at this
              omega
            rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
            simp only [hsh, if_true]
            exact hres
          · simp only [hsh, if_true] at hHigh
            obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
            have hck : ck ≤ st0.clock := by
              have := congrArg PanSemStateFiniteExact.clock hst
              simp only [emptyLocalsHOLFinite, setKvar_clock] at this
              omega
            rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
            simp only [hsh, if_true]
            exact hres
          · by_cases hv : isValidValueHOLExact u.toExact k n v = true
            · simp only [hsh, hv, if_true] at hHigh
              obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
              have hck : ck ≤ st0.clock := by
                have := congrArg PanSemStateFiniteExact.clock hst
                simp only [emptyLocalsHOLFinite, setKvar_clock] at this
                omega
              rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
              simp only [hsh, hv, if_true]
              exact hres
            · simp only [hsh, hv, if_true, if_false, Bool.false_eq_true] at hHigh
              obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
              have hck : ck ≤ st0.clock := by
                have := congrArg PanSemStateFiniteExact.clock hst
                simp only [emptyLocalsHOLFinite, setKvar_clock] at this
                omega
              rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
              simp only [hsh, hv, if_true, if_false, Bool.false_eq_true]
              exact hres
        · simp only [hsh, if_false, Bool.false_eq_true] at hHigh
          obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
          have hck : ck ≤ st0.clock := by
            have := congrArg PanSemStateFiniteExact.clock hst
            simp only [emptyLocalsHOLFinite, setKvar_clock] at this
            omega
          rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
          simp only [hsh, if_false, Bool.false_eq_true]
          exact hres
      · rcases info with _ | ⟨x1, _ | ⟨hid, hv, hp⟩⟩
        · simp only at hHigh
          obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
          have hck : ck ≤ st0.clock := by
            have := congrArg PanSemStateFiniteExact.clock hst
            simp only [emptyLocalsHOLFinite, setKvar_clock] at this
            omega
          rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
          simp only []
          exact hres
        · simp only at hHigh
          obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
          have hck : ck ≤ st0.clock := by
            have := congrArg PanSemStateFiniteExact.clock hst
            simp only [emptyLocalsHOLFinite, setKvar_clock] at this
            omega
          rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
          simp only []
          exact hres
        · by_cases hid' : e = hid
          · subst hid'
            cases hsh : u.eshapes.lookup e with
            | none =>
                simp only [if_true, hsh] at hHigh
                obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
                have hck : ck ≤ st0.clock := by
                  have := congrArg PanSemStateFiniteExact.clock hst
                  simp only [emptyLocalsHOLFinite, setKvar_clock] at this
                  omega
                rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
                simp only [if_true, hsh]
                exact hres
            | some sh =>
                by_cases hcond : (shapeEqHOL (shapeOfHOLExact v) sh &&
                    isValidValueHOLExact u.toExact VarKind.local hv v) = true
                · simp only [if_true, hsh, hcond] at hHigh
                  have hbound := evaluateHOLFiniteState_clock_le_result _ _ _ _ hHigh
                  simp only [setVarHOLFinite] at hbound
                  have hck : ck ≤ st0.clock := by omega
                  rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
                  simp only [if_true, hsh, hcond]
                  obtain ⟨hs1, hs2⟩ := Bool.and_eq_true_iff.mp hcond
                  have hmc := ihH values prog nl rsh st0 e v x1 e hv hp sh hargs hlk hc0 hb rfl rfl
                    hsh ((shapeEqHOL_eq_true _ _).mp hs1) hs2 res st ck hHigh hnt
                  have hstate : setVarHOLFinite hv v
                      { ({ st0 with clock := st0.clock - ck } : PanSemStateFiniteExact width σ) with
                        locals := u.locals } =
                      { setVarHOLFinite hv v { st0 with locals := u.locals } with
                        clock := (setVarHOLFinite hv v { st0 with locals := u.locals }).clock - ck } := rfl
                  rw [hstate, hmc]
                · simp only [if_true, hsh, hcond, if_false, Bool.false_eq_true] at hHigh
                  obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
                  have hck : ck ≤ st0.clock := by
                    have := congrArg PanSemStateFiniteExact.clock hst
                    simp only [emptyLocalsHOLFinite, setKvar_clock] at this
                    omega
                  rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
                  simp only [if_true, hsh, hcond, if_false, Bool.false_eq_true]
                  exact hres
          · simp only [hid', if_false] at hHigh
            obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
            have hck : ck ≤ st0.clock := by
              have := congrArg PanSemStateFiniteExact.clock hst
              simp only [emptyLocalsHOLFinite, setKvar_clock] at this
              omega
            rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
            simp only [hid', if_false]
            exact hres
      · simp only at hHigh
        obtain ⟨hres, hst⟩ := Prod.mk.inj hHigh
        have hck : ck ≤ st0.clock := by
          have := congrArg PanSemStateFiniteExact.clock hst
          simp only [emptyLocalsHOLFinite, setKvar_clock] at this
          omega
        rw [if_neg (hlow0 hck), lowCallee hck (by simp)]
        simp only
        exact hres

/-- The `PanPropsEvalStateFiniteExact` form of the `evaluate_clock_sub` motive
    (the property proved by the tagged cases). -/
abbrev clockSubAtHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (program : ProgHOL width) : Prop :=
  ∀ (result : Option (PanSemResultExact width))
    (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state program =
      (result, { st with clock := st.clock + ck }) →
    result ≠ some .timeOut →
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { state with clock := state.clock - ck } program = (result, st)

theorem mc_of_pair {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateFiniteExact width σ) (p : ProgHOL width)
    (h : clockSubAtHOLFinite (PanPropsEvalStateFiniteExact.ofPanSemFinite u) p) : Mc u p := by
  classical
  intro res st ck hrun hnt
  have hpair : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      (PanPropsEvalStateFiniteExact.ofPanSemFinite u) p =
      (res, { PanPropsEvalStateFiniteExact.ofPanSemFinite st with
        clock := (PanPropsEvalStateFiniteExact.ofPanSemFinite st).clock + ck }) := by
    simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
      PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite, hrun]
    rfl
  have e := congrArg (fun q => (q.1, q.2.toPanSemFinite)) (h res _ ck hpair hnt)
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at e
  exact e

theorem pair_of_mc {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (p : ProgHOL width)
    (h : Mc state.toPanSemFinite p) : clockSubAtHOLFinite state p := by
  classical
  intro result st ck hRun hnt
  have hCan : evaluateHOLFiniteState state.toPanSemFinite p =
      (result, { st.toPanSemFinite with clock := st.toPanSemFinite.clock + ck }) := by
    have e := congrArg (fun pair => (pair.1, pair.2.toPanSemFinite)) hRun
    simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
      PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at e
    exact e
  have hLow := h _ _ _ hCan hnt
  have hstate : ({ state with clock := state.clock - ck } :
      PanPropsEvalStateFiniteExact width σ).toPanSemFinite =
      { state.toPanSemFinite with clock := state.toPanSemFinite.clock - ck } := rfl
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, hstate, hLow,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]

theorem evalList_eq_mapM {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateFiniteExact width σ) (args : List (ExpHOL width)) :
    evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args =
      args.mapM (fun e => evalHOLFinite u
        (h := fun a => Classical.propDecidable (u.memaddrs a)) e) := by
  simp only [evalListHOLFinite_eq_toExact]
  induction args with
  | nil => rfl
  | cons e rest ih =>
      simp only [evalListHOLExact, List.mapM_cons, ih]
      simp only [evalHOLFinite]
      split
      · rename_i h1 h2; simp only [h1, h2]; rfl
      · rename_i h
        symm
        show Option.bind _ _ = none
        rw [Option.bind_eq_none_iff]
        intro a ha
        show Option.bind _ _ = none
        rw [Option.bind_eq_none_iff]
        intro b hb
        exact absurd hb (h a b ha)

end EvaluateClockSubCall

namespace EvaluateClockSubCallWitness
/-- Same-module canonical witness for the `locals`/`globals`/`code`/`eshapes`
    finite-map qualifier of the case theorem below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanPropsEvalStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
        PanPropsEvalStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanPropsEvalStateFiniteExact.holFmapAsFiniteSupportWitness
end EvaluateClockSubCallWitness

open EvaluateClockSubCall

/-- HOL `evaluate_ind`'s guarded Call callee premise at the `evaluate_clock_sub`
    motive, spelled as the reviewed `evaluate_invariants` Call premise
    (`EvalInvariant.lean`), with the clock-sub motive in place of the
    invariants motive. -/
abbrev clockSubCallCalleeIH {width : Nat} {σ : Type}
    [NeZero width] (function : MlS) (arguments : List (ExpHOL width))
    (state : PanPropsEvalStateFiniteExact width σ) :
    Prop :=
  ∀ (args : List (ValueHOL width))
    (v7 : ProgHOL width × (HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL))
    (prog : ProgHOL width)
    (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (return_sh : ShapeHOL),
    arguments.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite state.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (state.toPanSemFinite.memaddrs address)) expression) = some args →
    PanSemStateFiniteExact.lookupCodeHOLFinite state.toPanSemFinite.code.lookup
      function args = some (v7.1, v7.2.1, v7.2.2) →
    v7 = (prog, v12) →
    v12 = (newlocals, return_sh) →
    state.toPanSemFinite.clock ≠ 0 →
    clockSubAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.callEntryStateHOLFinite state.toPanSemFinite newlocals)) prog

/-- HOL `evaluate_ind`'s guarded Call handler premise at the `evaluate_clock_sub`
    motive, in the same binder-aligned spelling. -/
abbrev clockSubCallHandlerIH {width : Nat} {σ : Type}
    [NeZero width] (info : Option (Option (VarKind × MlS) ×
      Option (MlS × MlS × ProgHOL width))) (function : MlS)
    (arguments : List (ExpHOL width)) (state : PanPropsEvalStateFiniteExact width σ) :
    Prop :=
  ∀ (args : List (ValueHOL width))
    (v7 : ProgHOL width × (HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL))
    (prog : ProgHOL width)
    (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (return_sh : ShapeHOL)
    (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (v4 : Option (PanSemResultExact width))
    (st : PanSemStateFiniteExact width σ)
    (v8 : PanSemResultExact width) (eid : MlS) (exn : ValueHOL width)
    (v : Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))
    (v1 : Option (VarKind × MlS)) (v2 : Option (MlS × MlS × ProgHOL width))
    (v3 : MlS × MlS × ProgHOL width) (eid' : MlS)
    (v5 : MlS × ProgHOL width) (evar : MlS) (p : ProgHOL width) (sh : ShapeHOL),
    arguments.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite state.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (state.toPanSemFinite.memaddrs address)) expression) = some args →
    PanSemStateFiniteExact.lookupCodeHOLFinite state.toPanSemFinite.code.lookup
      function args = some (v7.1, v7.2.1, v7.2.2) →
    v7 = (prog, v12) →
    v12 = (newlocals, return_sh) →
    state.toPanSemFinite.clock ≠ 0 →
    eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.callEntryStateHOLFinite state.toPanSemFinite newlocals) prog →
    eval_prog = (v4, st) →
    v4 = some v8 →
    v8 = .exception eid exn →
    info = some v →
    v = (v1, v2) →
    v2 = some v3 →
    v3 = (eid', v5) →
    v5 = (evar, p) →
    eid = eid' →
    state.toPanSemFinite.eshapes.lookup eid = some sh →
    shapeOfHOLExact exn = sh →
    isValidValueHOLExact state.toPanSemFinite.toExact VarKind.local evar exn = true →
    clockSubAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.setVarHOLFinite evar exn
          { st with locals := state.toPanSemFinite.locals })) p


/-- `Call` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`),
    with exactly the two guarded `evaluate_ind` Call premises (handler and
    callee) at the clock-sub motive, in the statement shape of the accepted
    cases.  The proof (`callCore`) shows that the clock-subtracted run cannot
    time out: the callee IH aligns the callee run, the handler IH the matched
    exception handler, and `evaluate_clock` bounds `ck` below the callee's
    remaining clock.  `evaluate_add_clock_eq` then lifts the low run back to
    the given one. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubCallCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.call info function arguments : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      clockSubCallHandlerIH info function arguments state →
      clockSubCallCalleeIH function arguments state →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.call info function arguments) =
          (result, st) := by
  classical
  intro state result st ck hRun hnt ihH ihC
  refine pair_of_mc state _ ?_ result st ck hRun hnt
  apply callCore
  · intro values prog nl rsh hargs hlk hc0
    apply mc_of_pair
    exact ihC values (prog, (nl, rsh)) prog (nl, rsh) nl rsh
      (by rw [← evalList_eq_mapM]; exact hargs) hlk rfl rfl hc0
  · intro values prog nl rsh st0 eid exn v1 hid hv hp sh hargs hlk hc0 hb hinfo heid hsh hshape hvalid
    apply mc_of_pair
    exact ihH values (prog, (nl, rsh)) prog (nl, rsh) nl rsh (some (.exception eid exn), st0)
      (some (.exception eid exn)) st0 (.exception eid exn) eid exn (v1, some (hid, hv, hp)) v1
      (some (hid, hv, hp)) (hid, hv, hp) hid (hv, hp) hv hp sh
      (by rw [← evalList_eq_mapM]; exact hargs) hlk rfl rfl hc0 hb.symm rfl rfl rfl hinfo rfl rfl
      rfl rfl heid hsh hshape hvalid

end Flapjack
