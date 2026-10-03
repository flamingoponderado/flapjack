import Flapjack.Pancake.Proofs.PanSimp.CodeUpdate
import Flapjack.Pancake.Proofs.PanSimp.CompileSameState
import Flapjack.Pancake.Proofs.PanSimp.StateRel

/-!
The original pan_simp `compile_correct` (pan_simpProofScript.sml:654-1015).
Because `evaluate_seq_assoc` makes `seq_assoc Skip` semantically the identity,
the theorem is the simulation of a source state by the same state whose code
map holds the compiled function bodies (`state_rel_def`). The simulation is
proved for every program by the source's `evaluate_ind`; it carries the code
map explicitly (`CodeSim`), which is Flapjack proof infrastructure.
-/

namespace Flapjack.PanSimp

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

namespace CompileCorrectSupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end CompileCorrectSupport

/-- The code-map conjuncts of `state_rel_def`: the compiled code map has
exactly the source functions, with compiled bodies. -/
def CodeRel {width : Nat} [NeZero width]
    (scode c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    Prop :=
  (∀ f, scode.lookup f = none → c.lookup f = none) ∧
  (∀ f vshs prog rshape, scode.lookup f = some (vshs, prog, rshape) →
    c.lookup f = some (vshs, panSimpCompileHOL prog, rshape))

/-- The simulation statement for one program and source state: a non-Error
source run is matched with the same result by the code-updated state, and the
source run preserves the code map. -/
def CodeSim {width : Nat} {σ : Type} [NeZero width]
    (x : ProgHOL width × PanSemStateFiniteExact width σ) : Prop :=
  ∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)),
    evaluateHOLFiniteState x.2 x.1 = (res, s1) → res ≠ some .error → CodeRel x.2.code c →
    evaluateHOLFiniteState { x.2 with code := c } x.1 = (res, { s1 with code := c }) ∧
      s1.code = x.2.code

theorem codeSim_atomic {width : Nat} {σ : Type} [NeZero width] (p : ProgHOL width)
    (hCU : ∀ (st : PanSemStateFiniteExact width σ)
      (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
      (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      evaluateHOLFiniteState st p = (res, post) →
      evaluateHOLFiniteState { st with code := c } p = (res, { post with code := c }))
    (s : PanSemStateFiniteExact width σ) : CodeSim (p, s) := by
  intro res s1 c hev _ _
  refine ⟨hCU s c res s1 hev, ?_⟩
  have h := hCU s s.code res s1 hev
  have hs : ({ s with code := s.code } : PanSemStateFiniteExact width σ) = s := rfl
  rw [hs, hev] at h
  exact congrArg (fun x => x.2.code) h

theorem codeSim_dec {width : Nat} {σ : Type} [NeZero width]
    (v : MlS) (sh : ShapeHOL) (e : ExpHOL width) (prog : ProgHOL width)
    (s : PanSemStateFiniteExact width σ)
    (ih : ∀ value : ValueHOL width,
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some value ∧
        sh = shapeOfHOLExact value →
      CodeSim (prog, { s with locals := s.locals.update (v, value) })) :
    CodeSim (.dec v sh e prog, s) := by
  classical
  intro res post c heval hres hc
  dsimp only at heval hc ⊢
  rw [evaluateHOLFiniteState_dec_total] at heval
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only at heval ⊢
  have hcode := @evalHOLFinite_upd_code_eq width σ _ s
    (fun address => Classical.propDecidable (s.memaddrs address)) c e
  simp only [evalHOLFinite] at hcode
  rw [hcode]
  cases he : @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) e with
  | none =>
      simp only [he] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      exact absurd rfl hres
  | some value =>
      simp only [he] at heval ⊢
      by_cases hs : shapeEqHOL sh (shapeOfHOLExact value) = true
      · simp only [hs, if_true, setVarHOLFinite] at heval ⊢
        cases hb : evaluateHOLFiniteState { s with locals := s.locals.update (v, value) } prog with
        | mk r1 s1 =>
            rw [hb] at heval
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            obtain ⟨ht, hcd⟩ := ih value ⟨he, (shapeEqHOL_eq_true _ _).mp hs⟩ r1 s1 c hb hres hc
            dsimp only at ht hcd
            rw [ht]
            exact ⟨rfl, hcd⟩
      · simp only [hs] at heval
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact absurd rfl hres

theorem codeSim_seq {width : Nat} {σ : Type} [NeZero width]
    (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (ih2 : ∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
      (res, s1) = evaluateHOLFiniteState s c1 ∧ res = none → CodeSim (c2, s1))
    (ih1 : CodeSim (c1, s)) :
    CodeSim (.seq c1 c2, s) := by
  intro res post c heval hres hc
  dsimp only at heval hc ⊢
  rw [evaluateHOLFiniteState_seq_line780] at heval
  rw [evaluateHOLFiniteState_seq_line780]
  cases hfirst : evaluateHOLFiniteState s c1 with
  | mk r1 s1 =>
      rw [hfirst] at heval
      cases r1 with
      | none =>
          obtain ⟨ht, hcd⟩ := ih1 none s1 c hfirst (by simp) hc
          dsimp only at ht hcd
          rw [ht]
          dsimp only at heval ⊢
          obtain ⟨ht2, hcd2⟩ := ih2 none s1 ⟨hfirst.symm, rfl⟩ res post c heval hres
            (by dsimp only; rw [hcd]; exact hc)
          dsimp only at ht2 hcd2
          exact ⟨ht2, hcd2.trans hcd⟩
      | some r =>
          dsimp only at heval
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          obtain ⟨ht, hcd⟩ := ih1 (some r) s1 c hfirst hres hc
          dsimp only at ht hcd
          rw [ht]
          exact ⟨rfl, hcd⟩

theorem codeSim_ite {width : Nat} {σ : Type} [NeZero width]
    (e : ExpHOL width) (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (ih : ∀ (v1 : ValueHOL width) (v6 : HolWordLab width) (w : BitVec width),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v1 ∧
        v1 = .val v6 ∧ v6 = .word w →
      CodeSim (if w ≠ 0 then c1 else c2, s)) :
    CodeSim (.ite e c1 c2, s) := by
  classical
  intro res post c heval hres hc
  dsimp only at heval hc ⊢
  rw [evaluateHOLFiniteState_ite] at heval
  rw [evaluateHOLFiniteState_ite]
  have hcode := @evalHOLFinite_upd_code_eq width σ _ s
    (fun address => Classical.propDecidable (s.memaddrs address)) c e
  simp only [evalHOLFinite] at hcode
  rw [hcode]
  cases he : @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) e with
  | none =>
      simp only [he] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      exact absurd rfl hres
  | some value =>
      cases value with
      | val lab =>
          cases lab with
          | word w =>
              simp only [he] at heval ⊢
              have hb := ih _ _ w ⟨he, rfl, rfl⟩
              by_cases hw : w = 0
              · rw [if_pos hw] at heval ⊢
                rw [if_neg (fun h' => h' hw)] at hb
                exact hb res post c heval hres hc
              · rw [if_neg hw] at heval ⊢
                rw [if_pos hw] at hb
                exact hb res post c heval hres hc
      | rStruct _ | nStruct _ _ =>
          simp only [he] at heval
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          exact absurd rfl hres

theorem codeSim_while {width : Nat} {σ : Type} [NeZero width]
    (e : ExpHOL width) (body : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (ihContinue : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
        (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
        (v1 : PanSemResultExact width),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
        (res, s1) = evaluateHOLFiniteState s.decClockHOLFinite body ∧
        res = some v1 ∧ v1 = .continue →
      CodeSim (.while e body, s1))
    (ihNone : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
        (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
        (res, s1) = evaluateHOLFiniteState s.decClockHOLFinite body ∧ res = none →
      CodeSim (.while e body, s1))
    (ihBody : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 →
      CodeSim (body, s.decClockHOLFinite)) :
    CodeSim (.while e body, s) := by
  classical
  intro res post c heval hres hc
  dsimp only at heval hc ⊢
  rw [evaluateHOLFiniteState_while_fixClockRewrite] at heval
  rw [evaluateHOLFiniteState_while_fixClockRewrite]
  simp only [evalHOLFinite] at heval ⊢
  have hcode := @evalHOLFinite_upd_code_eq width σ _ s
    (fun address => Classical.propDecidable (s.memaddrs address)) c e
  simp only [evalHOLFinite] at hcode
  rw [hcode]
  cases he : @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) e with
  | none =>
      simp only [he] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      exact absurd rfl hres
  | some value =>
      cases value with
      | rStruct _ | nStruct _ _ =>
          simp only [he] at heval
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          exact absurd rfl hres
      | val lab =>
          cases lab with
          | word w =>
              simp only [he] at heval ⊢
              by_cases hw : w ≠ 0
              · simp only [hw, if_true, ne_eq, not_false_eq_true] at heval ⊢
                by_cases hz : s.clock = 0
                · simp only [hz, if_true] at heval ⊢
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                  exact ⟨by simp only [emptyLocalsHOLFinite, hz], rfl⟩
                · simp only [hz, if_false] at heval ⊢
                  cases hb : evaluateHOLFiniteState s.decClockHOLFinite body with
                  | mk r1 s1 =>
                      simp only [hb] at heval
                      have hr1 : r1 ≠ some .error := by
                        rintro rfl; obtain ⟨rfl, -⟩ := Prod.mk.inj heval; exact hres rfl
                      obtain ⟨ht, hcd⟩ := ihBody (.val (.word w)) (.word w) w
                        ⟨he, rfl, rfl, hw, hz⟩ r1 s1 c hb hr1 hc
                      have ht' : evaluateHOLFiniteState
                          ({ s with code := c }).decClockHOLFinite body =
                          (r1, { s1 with code := c }) := by
                        simpa only [decClockHOLFinite] using ht
                      rw [ht']
                      dsimp only at hcd
                      have hc1 : CodeRel s1.code c := by rw [hcd]; exact hc
                      cases r1 with
                      | none =>
                          obtain ⟨ht2, hcd2⟩ := ihNone (.val (.word w)) (.word w) w none s1
                            ⟨he, rfl, rfl, hw, hz, hb.symm, rfl⟩ res post c heval hres hc1
                          exact ⟨ht2, hcd2.trans hcd⟩
                      | some result =>
                          cases result with
                          | «continue» =>
                              obtain ⟨ht2, hcd2⟩ := ihContinue (.val (.word w)) (.word w) w
                                (some .continue) s1 .continue
                                ⟨he, rfl, rfl, hw, hz, hb.symm, rfl, rfl⟩ res post c heval hres hc1
                              exact ⟨ht2, hcd2.trans hcd⟩
                          | «break» =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              exact ⟨rfl, hcd⟩
                          | error | timeOut | returned _ | exception _ _ | finalFfi _ =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              exact ⟨rfl, hcd⟩
              · simp only [hw, if_false] at heval ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                exact ⟨rfl, rfl⟩

/-- Argument evaluation does not read the code map. -/
theorem evalListCodeUpd {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (state : PanSemStateFiniteExact width σ) (expressions : List (ExpHOL width)) :
    evalListHOLFinite { state with code := c }
      (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions =
    evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions := by
  classical
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
      simp only [evalListHOLFinite, evalListHOLExact] at ih ⊢
      rw [ih]
      have h := congrFun (@evalHOL_upd_code_eta width σ _ state
        (fun address => Classical.propDecidable (state.memaddrs address)) c) expression
      simp only [evalHOLFinite] at h
      rw [h]

/-- Under `CodeRel`, function lookup finds the compiled body with the same
parameters, callee locals and return shape. -/
theorem lookupCodeRel {width : Nat} [NeZero width]
    (scode c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (hc : CodeRel scode c) (name : MlS) (args : List (ValueHOL width)) :
    lookupCodeHOLFinite c.lookup name args =
      (lookupCodeHOLFinite scode.lookup name args).map (fun entry =>
        (panSimpCompileHOL entry.1, entry.2.1, entry.2.2)) := by
  have hraw : lookupCodeHOLExact c.lookup name args =
      (lookupCodeHOLExact scode.lookup name args).map (fun entry =>
        (panSimpCompileHOL entry.1, entry.2.1, entry.2.2)) := by
    unfold lookupCodeHOLExact
    cases h : scode.lookup name with
    | none => simp [hc.1 name h]
    | some entry =>
        obtain ⟨params, body, shape⟩ := entry
        rw [hc.2 name params body shape h]
        simp only
        split <;> simp_all
  let project := fun (entry : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL) =>
    (entry.1, entry.2.1.lookup, entry.2.2)
  have hinj : Function.Injective project := by
    rintro ⟨p1,l1,s1⟩ ⟨p2,l2,s2⟩ h
    simp only [project, Prod.mk.injEq] at h
    obtain ⟨rfl, hl, rfl⟩ := h
    have hm : l1 = l2 := HolFiniteMapExact.ext hl
    subst l2
    rfl
  apply Option.map_injective hinj
  have w := PanSemStateFiniteExact.holFmapAsFiniteSupportHeterogeneousFunctionWitness_lookupCodeCanonicalHOL
    (width := width)
  simp only [PanSemStateFiniteExact.lookupCodeCanonicalHOL] at w
  rw [w, Option.map_map]
  change _ = Option.map ((fun (entry : ProgHOL width × (MlS → Option (ValueHOL width)) × ShapeHOL) =>
    (panSimpCompileHOL entry.1, entry.2.1, entry.2.2)) ∘ project)
      (lookupCodeHOLFinite scode.lookup name args)
  rw [← Option.map_map, w]
  exact hraw

/-- The callee body: a non-Error source run of `prog` is matched by the
compiled body in the code-updated entry state. -/
theorem codeSim_body {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (prog : ProgHOL width)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (hc : CodeRel s.code c)
    (ih : CodeSim (prog, { s.decClockHOLFinite with locals := newlocals }))
    (r : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s newlocals) prog = (r, st))
    (hr : r ≠ some .error) :
    evaluateHOLFiniteState (callEntryStateHOLFinite { s with code := c } newlocals)
        (panSimpCompileHOL prog) = (r, { st with code := c }) ∧ st.code = s.code := by
  obtain ⟨ht, hcd⟩ := ih r st c hb hr hc
  have ht' : evaluateHOLFiniteState (callEntryStateHOLFinite { s with code := c } newlocals) prog =
      (r, { st with code := c }) := ht
  refine ⟨?_, hcd⟩
  rw [compileCorrectSameStateHOL _ _ (by rw [ht']; exact hr), ht']

theorem codeSim_call {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (argexps : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ)
    (ihHandler : ∀ (args : List (ValueHOL width))
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
        lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
        v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 ∧
        eval_prog = evaluateHOLFiniteState
          { s.decClockHOLFinite with locals := newlocals } prog ∧
        eval_prog = (v4, st) ∧ v4 = some v8 ∧ v8 = .exception eid exn ∧
        info = some v ∧ v = (v1, v2) ∧ v2 = some v3 ∧ v3 = (eid', v5) ∧
        v5 = (evar, p) ∧ eid = eid' ∧ s.eshapes.lookup eid = some sh ∧
        shapeOfHOLExact exn = sh ∧ isValidValueHOLExact s.toExact .local evar exn = true →
      CodeSim (p, setVarHOLFinite evar exn { st with locals := s.locals }))
    (ihBody : ∀ (args : List (ValueHOL width))
        (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
      s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address))
          argexps = some args ∧
        lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
        v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
      CodeSim (prog, { s.decClockHOLFinite with locals := newlocals })) :
    CodeSim (.call info fname argexps, s) := by
  classical
  intro res post c heval hres hc
  dsimp only at heval hc ⊢
  have validCode : ∀ kind evar value,
      isValidValueHOLExact { s with code := c }.toExact kind evar value =
        isValidValueHOLExact s.toExact kind evar value := by
    intro kind evar value
    cases kind <;> rfl
  rw [evaluateHOLFiniteState_call] at heval
  rw [evaluateHOLFiniteState_call, evalListCodeUpd]
  cases ha : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) argexps with
  | none =>
      simp only [ha] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      exact absurd rfl hres
  | some values =>
    simp only [ha] at heval ⊢
    rw [lookupCodeRel s.code c hc]
    cases hl : lookupCodeHOLFinite s.code.lookup fname values with
    | none =>
        simp only [hl] at heval
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact absurd rfl hres
    | some triple =>
      obtain ⟨prog, newlocals, rsh⟩ := triple
      simp only [hl, Option.map_some] at heval ⊢
      by_cases hz : s.clock = 0
      · simp only [hz, if_true] at heval ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact ⟨by simp only [emptyLocalsHOLFinite, hz], rfl⟩
      · simp only [hz, if_false] at heval ⊢
        cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s newlocals) prog with
        | mk r st =>
        rw [hb] at heval
        have hr : r ≠ some .error := by
          rintro rfl
          obtain ⟨rfl, -⟩ := Prod.mk.inj heval
          exact hres rfl
        obtain ⟨hcomp, hcd⟩ := codeSim_body s newlocals prog c hc
          (ihBody values _ prog _ newlocals rsh ⟨ha, hl, rfl, rfl, hz⟩) r st hb hr
        rw [hcomp]
        simp only [validCode]
        cases r with
        | none =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            exact absurd rfl hres
        | some result =>
          cases result with
          | «break» | «continue» | error =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact absurd rfl hres
          | timeOut | finalFfi _ =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact ⟨rfl, hcd⟩
          | returned value =>
            by_cases hs : shapeEqHOL (shapeOfHOLExact value) rsh = true
            · simp only [hs, if_true] at heval ⊢
              cases info with
              | none =>
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                  exact ⟨rfl, hcd⟩
              | some pair =>
                obtain ⟨destination, handler⟩ := pair
                cases destination with
                | none =>
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                    exact ⟨rfl, hcd⟩
                | some pair =>
                  obtain ⟨kind, evar⟩ := pair
                  dsimp only at heval ⊢
                  by_cases hv : isValidValueHOLExact s.toExact kind evar value = true
                  · simp only [hv, if_true] at heval ⊢
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                    cases kind <;> exact ⟨rfl, hcd⟩
                  · simp only [hv, Bool.false_eq_true, if_false] at heval
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                    exact absurd rfl hres
            · simp only [hs, Bool.false_eq_true, if_false] at heval
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact absurd rfl hres
          | exception eid value =>
            cases info with
            | none =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                exact ⟨rfl, hcd⟩
            | some pair =>
              obtain ⟨destination, handler⟩ := pair
              cases handler with
              | none =>
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                  exact ⟨rfl, hcd⟩
              | some triple =>
                obtain ⟨handlerId, evar, handler⟩ := triple
                dsimp only at heval ⊢
                by_cases hid : eid = handlerId
                · subst handlerId
                  simp only [if_true] at heval ⊢
                  cases he : s.eshapes.lookup eid with
                  | none =>
                      simp only [he] at heval
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                      exact absurd rfl hres
                  | some handlerShape =>
                    simp only [he] at heval ⊢
                    by_cases hv : (shapeEqHOL (shapeOfHOLExact value) handlerShape &&
                        isValidValueHOLExact s.toExact .local evar value) = true
                    · simp only [hv, if_true] at heval ⊢
                      have hh := hv
                      simp only [Bool.and_eq_true] at hh
                      obtain ⟨hshape, hvalid⟩ := hh
                      have hsim := ihHandler values _ prog _ newlocals rsh (some (.exception eid value), st)
                        _ st _ eid value _ destination _ _ eid _ evar handler handlerShape
                        ⟨ha, hl, rfl, rfl, hz, hb.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, he,
                          (shapeEqHOL_eq_true _ _).mp hshape, hvalid⟩
                      obtain ⟨ht2, hcd2⟩ := hsim res post c heval hres
                        (by simp only [setVarHOLFinite]; rw [hcd]; exact hc)
                      exact ⟨by simpa only [setVarHOLFinite] using ht2,
                        hcd2.trans (by simp only [setVarHOLFinite]; exact hcd)⟩
                    · simp only [hv, Bool.false_eq_true, if_false] at heval
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                      exact absurd rfl hres
                · simp only [hid, if_false] at heval ⊢
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                  exact ⟨rfl, hcd⟩

theorem codeSim_decCall {width : Nat} {σ : Type} [NeZero width]
    (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
    (prog1 : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (ihCont : ∀ (args : List (ValueHOL width))
        (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL)
        (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
        (v : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
        (v3 : PanSemResultExact width) (retv : ValueHOL width),
      s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address))
          argexps = some args ∧
        lookupCodeHOLFinite s.code.lookup fname args = some v2 ∧
        v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ s.clock ≠ 0 ∧
        eval_prog = evaluateHOLFiniteState
          { s.decClockHOLFinite with locals := newlocals } prog ∧
        eval_prog = (v, st) ∧ v = some v3 ∧ v3 = .returned retv ∧
        shapeOfHOLExact retv = shape ∧ shapeOfHOLExact retv = return_sh →
      CodeSim (prog1, setVarHOLFinite rt retv { st with locals := s.locals }))
    (ihBody : ∀ (args : List (ValueHOL width))
        (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
      s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address))
          argexps = some args ∧
        lookupCodeHOLFinite s.code.lookup fname args = some v2 ∧
        v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
      CodeSim (prog, { s.decClockHOLFinite with locals := newlocals })) :
    CodeSim (.decCall rt shape fname argexps prog1, s) := by
  classical
  intro res post c heval hres hc
  dsimp only at heval hc ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at heval
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, evalListCodeUpd]
  cases ha : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) argexps with
  | none =>
      simp only [ha] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      exact absurd rfl hres
  | some values =>
    simp only [ha] at heval ⊢
    rw [lookupCodeRel s.code c hc]
    cases hl : lookupCodeHOLFinite s.code.lookup fname values with
    | none =>
        simp only [hl] at heval
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact absurd rfl hres
    | some triple =>
      obtain ⟨prog, newlocals, rsh⟩ := triple
      simp only [hl, Option.map_some] at heval ⊢
      by_cases hz : s.clock = 0
      · simp only [hz, if_true] at heval ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact ⟨by simp only [emptyLocalsHOLFinite, hz], rfl⟩
      · simp only [hz, if_false] at heval ⊢
        cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s newlocals) prog with
        | mk r st =>
        rw [hb] at heval
        dsimp only at heval
        have hr : r ≠ some .error := by
          rintro rfl
          obtain ⟨rfl, -⟩ := Prod.mk.inj heval
          exact hres rfl
        obtain ⟨hcomp, hcd⟩ := codeSim_body s newlocals prog c hc
          (ihBody values _ prog _ newlocals rsh ⟨ha, hl, rfl, rfl, hz⟩) r st hb hr
        rw [hcomp]
        dsimp only
        cases r with
        | none =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            exact absurd rfl hres
        | some result =>
          cases result with
          | «break» | «continue» | error =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact absurd rfl hres
          | timeOut | finalFfi _ | exception _ _ =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact ⟨rfl, hcd⟩
          | returned value =>
            by_cases hs : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) rsh) = true
            · simp only [hs, if_true] at heval ⊢
              have hh := hs
              simp only [Bool.and_eq_true] at hh
              obtain ⟨hs1, hs2⟩ := hh
              have hsim := ihCont values _ prog _ newlocals rsh (some (.returned value), st) _ st _ value
                ⟨ha, hl, rfl, rfl, hz, hb.symm, rfl, rfl, rfl,
                  (shapeEqHOL_eq_true _ _).mp hs1, (shapeEqHOL_eq_true _ _).mp hs2⟩
              cases hk : evaluateHOLFiniteState
                  (setVarHOLFinite rt value { st with locals := s.locals }) prog1 with
              | mk r2 st2 =>
              rw [hk] at heval
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              obtain ⟨ht2, hcd2⟩ := hsim r2 st2 c hk hres
                (by simp only [setVarHOLFinite]; rw [hcd]; exact hc)
              have ht2' : evaluateHOLFiniteState
                  (setVarHOLFinite rt value { st with code := c, locals := s.locals }) prog1 =
                  (r2, { st2 with code := c }) := by
                simpa only [setVarHOLFinite] using ht2
              rw [ht2']
              exact ⟨rfl, hcd2.trans (by simp only [setVarHOLFinite]; exact hcd)⟩
            · simp only [hs, Bool.false_eq_true, if_false] at heval
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact absurd rfl hres

/-- The code-map simulation for every program and state, by `evaluate_ind`. -/
theorem codeSimAll {width : Nat} {σ : Type} [NeZero width] :
    ∀ (prog : ProgHOL width) (s : PanSemStateFiniteExact width σ), CodeSim (prog, s) := by
  have key := evaluateIndHOL (σ := σ) (width := width) CodeSim
  refine fun prog s => key ⟨
    codeSim_atomic .skip (fun st c res post h => evaluateCodeUpd_Skip c st res post h),
    fun v sh e prog s ih => codeSim_dec v sh e prog s ih,
    fun vk v src => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_Assign c st vk v src res post h),
    fun v pop es => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_Primitive c st v pop es res post h),
    fun dst src => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_Store c st dst src res post h),
    fun dst src => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_Store32 c st dst src res post h),
    fun dst src => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_StoreByte c st dst src res post h),
    fun op vk v ad => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_ShMemLoad c st op vk v ad res post h),
    fun op ad e => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_ShMemStore c st op ad e res post h),
    fun c1 c2 s ih => codeSim_seq c1 c2 s ih.1 ih.2,
    fun e c1 c2 s ih => codeSim_ite e c1 c2 s ih,
    codeSim_atomic .break (fun st c res post h => evaluateCodeUpd_Break c st res post h),
    codeSim_atomic .continue (fun st c res post h => evaluateCodeUpd_Continue c st res post h),
    fun e c s ih => codeSim_while e c s ih.1 ih.2.1 ih.2.2,
    fun e => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_Return c st e res post h),
    fun eid e => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_Raise c st eid e res post h),
    codeSim_atomic .tick (fun st c res post h => evaluateCodeUpd_Tick c st res post h),
    fun v0 v1 => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_Annot c st v0 v1 res post h),
    fun info fname argexps s ih => codeSim_call info fname argexps s ih.1 ih.2,
    fun rt shape fname argexps prog1 s ih =>
      codeSim_decCall rt shape fname argexps prog1 s ih.1 ih.2,
    fun i p1 l1 p2 l2 => codeSim_atomic _
      (fun st c res post h => evaluateCodeUpd_ExtCall c st i p1 l1 p2 l2 res post h)⟩ prog s

/-- Original pan_simp `compile_correct`: the `evaluate_ind` instance of the
source goal at `comp = seq_assoc Skip`. A non-Error source run is matched, with
the same result, by the `state_rel`-related state running `seq_assoc Skip prog`,
and `state_rel` is re-established for the final states. The binders are
exactly those of the elaborated HOL theorem (`v v1 res s1 t`, captured with
types by `pan_simp_semantics_statement_probe`): the source `goal` term's
`∀ctxt` is removed by the `REWRITE_RULE []` that builds `ind_thm2`, so the
stored theorem has no `ctxt` quantifier. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (prog : ProgHOL width) (s : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width)) (s1 t : PanSemStateFiniteExact width σ),
      evaluateHOLFiniteState s prog = (res, s1) ∧ res ≠ some .error ∧
        stateRel s t t.code →
      ∃ t1, evaluateHOLFiniteState t (seqAssocHOL .skip prog) = (res, t1) ∧
        stateRel s1 t1 t1.code := by
  rintro prog s res s1 t ⟨hev, hres, ht, hnone, hsome⟩
  obtain ⟨hsim, hcd⟩ := codeSimAll prog s res s1 t.code hev hres ⟨hnone, hsome⟩
  refine ⟨{ s1 with code := t.code }, ?_, rfl, ?_, ?_⟩
  · rw [evaluateSeqAssocHOL, evaluateSkipSeqHOL, ht]
    exact hsim
  · intro f h
    exact hnone f (by rw [← hcd]; exact h)
  · intro f vshs p rshape h
    exact hsome f vshs p rshape (by rw [← hcd]; exact h)

end Flapjack.PanSimp
