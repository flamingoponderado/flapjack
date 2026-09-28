import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call

/-!
# `pc_compile_correct` While case over the exact carriers

The `While e c` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:2188-2242`): against `pcCompileCorrectAt`, then in HOL's own shape as the
tagged `pcCompileCorrect_While` (bead `flapjack-pxn.18.4.3.102`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)

/-- HOL `pc_compile_correct[While]` (`pan_to_crepProofScript.sml:2188-2242`)
    against `pcCompileCorrectAt`, from the three While IHs of the rebound
    `evaluate_ind`: `P (While e c, s1)` after the body completes with Continue or
    NONE, and `P (c, dec_clock s)` for the body, all under a nonzero condition
    and a positive clock. By the tagged `compile_exp_val_rel`, the compiled
    condition is a single expression that evaluates to the same word. A zero
    word exits normally; a zero clock times out on both sides. After the body,
    Break exits normally, Continue/NONE re-enter the loop through the recursive
    IHs, and every other result leaves the loop unchanged (`exit_loop` is the
    identity on it). No target run is assumed. Untagged: the tagged HOL-shaped
    statement is `pcCompileCorrect_While`. -/
theorem pcCompileCorrectAt_while {width : Nat} {σ : Type} [NeZero width]
    (e : ExpHOL width) (c : ProgHOL width) (source : PanSemStateFiniteExact width σ)
    (ihCont : ∀ (w : BitVec width) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLExact width σ _ source.toExact
          (fun address => Classical.propDecidable (source.memaddrs address)) e =
        some (.val (.word w)) → w ≠ 0 → source.clock ≠ 0 →
      (PanSemStateFiniteExact.decClockHOLFinite source).evaluateHOLFiniteState c =
        (some .continue, s1) →
      pcCompileCorrectAt (.while e c) s1)
    (ihNone : ∀ (w : BitVec width) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLExact width σ _ source.toExact
          (fun address => Classical.propDecidable (source.memaddrs address)) e =
        some (.val (.word w)) → w ≠ 0 → source.clock ≠ 0 →
      (PanSemStateFiniteExact.decClockHOLFinite source).evaluateHOLFiniteState c = (none, s1) →
      pcCompileCorrectAt (.while e c) s1)
    (ihBody : ∀ w : BitVec width,
      @evalHOLExact width σ _ source.toExact
          (fun address => Classical.propDecidable (source.memaddrs address)) e =
        some (.val (.word w)) → w ≠ 0 → source.clock ≠ 0 →
      pcCompileCorrectAt c (PanSemStateFiniteExact.decClockHOLFinite source)) :
    pcCompileCorrectAt (.while e c : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocs : localisedExpHOL e = true ∧ localisedProgHOL c = true := by
    simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite] at hrun
  split at hrun
  case h_2 =>
    exact absurd (Prod.mk.inj hrun).1.symm hres
  rename_i w heval
  rcases hc : compileExpExactHOLW ctxt e with ⟨es, sh⟩
  obtain ⟨hes, _, _, _⟩ :=
    @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) ctxt t
      (fun address => Classical.propDecidable (t.memaddrs address))
      e (.val (.word w)) es sh heval hstate hcode hlocals hlocs.1 hc
  obtain ⟨ce, hce⟩ : ∃ ce, es = [ce] := by
    rcases es with _ | ⟨ce, _ | ⟨_, _⟩⟩
    · simp [flattenHOL] at hes
    · exact ⟨ce, rfl⟩
    · simp [flattenHOL] at hes
  subst hce
  have hce : @evalCrepSemHOLExp width _ σ t
      (fun address => Classical.propDecidable (t.memaddrs address)) ce = some (.word w) := by
    simpa [flattenHOL] using hes
  have hcomp : ∀ ctxt' : PanToCrepContextExact width, ctxt' = ctxt →
      compileProgExactHOLW ctxt' (.while e c) = .while ce (compileProgExactHOLW ctxt' c) := by
    rintro _ rfl
    simp only [compileProgExactHOLW, compileWhileExactHOLW, hc]
  rw [hcomp ctxt rfl, evalCrepSemHOLProgExact_while_holShape, hce]
  dsimp only
  have hclk : source.clock = t.clock := hstate.2.2.2.2.2.1
  by_cases hw : w ≠ 0
  case neg =>
    rw [if_neg hw] at hrun ⊢
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    exact ⟨_, _, rfl, hstate, hcode, hexcp, rfl, hlocals⟩
  rw [if_pos hw] at hrun ⊢
  by_cases hck : source.clock = 0
  · rw [if_pos hck] at hrun
    rw [if_pos (hclk ▸ hck)]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    exact ⟨_, _, rfl, panToCrepStateRelFiniteExact_emptyLocals source t hstate, hcode, hexcp, rfl⟩
  rw [if_neg hck] at hrun
  rw [if_neg (hclk ▸ hck)]
  rcases hb : (PanSemStateFiniteExact.decClockHOLFinite source).evaluateHOLFiniteState c with
    ⟨r1, s'⟩
  rw [hb] at hrun
  dsimp only at hrun
  have hst' : panToCrepStateRelFiniteExact (PanSemStateFiniteExact.decClockHOLFinite source)
      (decClockCrepSemHOL t) := by
    simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.decClockHOLFinite,
      decClockCrepSemHOL, hclk] using hstate
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    exact absurd (Prod.mk.inj hrun).1.symm hres
  obtain ⟨res1, t1, hrun1, hs, hc', he, hrr⟩ :=
    ihBody w heval hw hck r1 s' (decClockCrepSemHOL t) ctxt hb hr1 hst' hcode hexcp hlocals
      hlocs.2
  rw [hrun1]
  dsimp only
  rcases r1 with _ | r1
  · obtain ⟨rfl, hl⟩ := hrr
    have := ihNone w s' heval hw hck hb res s1 t1 ctxt hrun hres hs hc' he hl hloc
    rwa [hcomp ctxt rfl] at this
  cases r1 with
  | error => exact absurd rfl hr1
  | «continue» =>
      obtain ⟨rfl, hl⟩ := hrr
      have := ihCont w s' heval hw hck hb res s1 t1 ctxt hrun hres hs hc' he hl hloc
      rwa [hcomp ctxt rfl] at this
  | «break» =>
      obtain ⟨rfl, hl⟩ := hrr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      exact ⟨_, _, rfl, hs, hc', he, rfl, hl⟩
  | timeOut =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      subst hrr
      exact ⟨_, _, rfl, hs, hc', he, rfl⟩
  | returned v =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      subst hrr
      exact ⟨_, _, rfl, hs, hc', he, rfl⟩
  | finalFfi f =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      subst hrr
      exact ⟨_, _, rfl, hs, hc', he, rfl⟩
  | exception eid v =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      simp only [pcCompileCorrectResultRel] at hrr
      split at hrr
      · exact hrr.elim
      rename_i n hn
      obtain ⟨rfl, hg⟩ := hrr
      refine ⟨_, _, rfl, hs, hc', he, ?_⟩
      simp only [pcCompileCorrectResultRel, hn]
      exact ⟨rfl, hg⟩

namespace PcCompileCorrectWhileWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged While case below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectWhileWitnesses

/-- HOL `pc_compile_correct`, `While` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:2188`).
    HOL's printed `evaluate_ind` While conjunct has three IHs, transcribed binder
    for binder and in HOL order, at `P = pcCompileCorrectAtHOL`:
    `!v2 v11 w res s1 v1. eval s e = SOME v2 /\ v2 = Val v11 /\ v11 = Word w /\
      w <> 0w /\ s.clock <> 0 /\ (res,s1) = evaluate (c,dec_clock s) /\
      res = SOME v1 /\ v1 = Continue ==> P (While e c,s1)`,
    `!v2 v11 w res s1. ... /\ res = NONE ==> P (While e c,s1)`, and
    `!v2 v11 w. ... ==> P (c,dec_clock s)`. `eval s` is the tagged exact
    expression evaluator with the classical address decision and `dec_clock` is
    the tagged `decClockHOLFinite`, as in the tagged Pan While arm
    (`evaluateHOLFiniteState_while_fixClockRewrite`). The conclusion is
    `P (While e c, s)` unfolded as in `pcCompileCorrectAtHOL`. The translation is
    the one reviewed for `pcCompileCorrect_Call`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_While {width : Nat} {σ : Type} [NeZero width] :
    ∀ (e : ExpHOL width) (c : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
          (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
          (v1 : PanSemResultExact width),
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
            (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
            res = some v1 ∧ v1 = .continue →
          pcCompileCorrectAtHOL (.while e c) s1) ∧
      (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
          (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
            (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
            res = none →
          pcCompileCorrectAtHOL (.while e c) s1) ∧
      (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 →
          pcCompileCorrectAtHOL c s.decClockHOLFinite) →
      ∀ (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.while e c : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.while e c : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.while e c : ProgHOL width)) =
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
  intro e c s ⟨ihCont, ihNone, ihBody⟩ res s1 t ctxt
    ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_while e c s
      (fun w s' hv hw hck hb => (pcCompileCorrectAt_iff_HOL _ _).mpr
        (ihCont _ _ w _ s' _ ⟨hv, rfl, rfl, hw, hck, hb.symm, rfl, rfl⟩))
      (fun w s' hv hw hck hb => (pcCompileCorrectAt_iff_HOL _ _).mpr
        (ihNone _ _ w _ s' ⟨hv, rfl, rfl, hw, hck, hb.symm, rfl⟩))
      (fun w hv hw hck => (pcCompileCorrectAt_iff_HOL _ _).mpr
        (ihBody _ _ w ⟨hv, rfl, rfl, hw, hck⟩))
      res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
