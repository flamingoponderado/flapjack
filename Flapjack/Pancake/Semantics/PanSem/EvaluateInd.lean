import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

/-!
# HOL `panSem$evaluate_ind` over the exact finite evaluator

HOL `evaluate_ind` (`cakeml/pancake/semantics/panSemScript.sml:777-778`) is the
induction principle of the clocked `evaluate`, rebound with
`fix_clock_evaluate`. Its 21 conjuncts give, for each constructor, `P (p, s)`
from `P` at the recursive calls `evaluate` makes. `evaluateIndHOL` states it over
the tagged total `evaluateHOLFiniteState`, the line-780 `evaluate_def`, with each
IH transcribed binder for binder from the checked-in HOL print
(`scripts/hol-probes/pan_sem_evaluate_ind_probe.out`).

The proof is well-founded recursion on `(s.clock, sizeOf p)`: every IH is at a
structurally smaller program whose state clock is no larger (the tagged
`evaluate_clock`), or at a strictly smaller clock (`dec_clock` before a loop body
re-entry or a call). No evaluator case analysis is needed.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpHOL ProgHOL ShapeHOL)

namespace PanSem.EvaluateIndWitness

/-- Same-module canonical carrier witness for the `fmap_as_finite_support`
    qualifier on `evaluateIndHOL` (the roundtrip of `PanSemStateFiniteExact`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end PanSem.EvaluateIndWitness

/-- The 21 conjuncts of HOL `evaluate_ind` for a predicate `P` on
    `(program, state)` pairs, in HOL order. Flapjack infrastructure naming the
    premise of `evaluateIndHOL`; the tagged theorem restates it literally. -/
def PanEvaluateIndHyps {width : Nat} {σ : Type} [NeZero width]
    (P : ProgHOL width × PanSemStateFiniteExact width σ → Prop) : Prop :=
  (∀ s, P (.skip, s)) ∧
  (∀ (v : MlS) (sh : ShapeHOL) (e : ExpHOL width) (prog : ProgHOL width)
      (s : PanSemStateFiniteExact width σ),
    (∀ value : ValueHOL width,
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some value ∧
        sh = shapeOfHOLExact value →
      P (prog, { s with locals := s.locals.update (v, value) })) →
    P (.dec v sh e prog, s)) ∧
  (∀ (vk : VarKind) (v : MlS) (src : ExpHOL width) s, P (.assign vk v src, s)) ∧
  (∀ (v : MlS) (pop : PrimOp) (es : List (ExpHOL width)) s, P (.primitive v pop es, s)) ∧
  (∀ (dst src : ExpHOL width) s, P (.store dst src, s)) ∧
  (∀ (dst src : ExpHOL width) s, P (.store32 dst src, s)) ∧
  (∀ (dst src : ExpHOL width) s, P (.storeByte dst src, s)) ∧
  (∀ (op : OpSize) (vk : VarKind) (v : MlS) (ad : ExpHOL width) s,
    P (.shMemLoad op vk v ad, s)) ∧
  (∀ (op : OpSize) (ad e : ExpHOL width) s, P (.shMemStore op ad e, s)) ∧
  (∀ (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ),
    (∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
        (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s c1 ∧ res = none →
        P (c2, s1)) ∧
      P (c1, s) →
    P (.seq c1 c2, s)) ∧
  (∀ (e : ExpHOL width) (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ),
    (∀ (v1 : ValueHOL width) (v6 : HolWordLab width) (w : BitVec width),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v1 ∧
        v1 = .val v6 ∧ v6 = .word w →
      P (if w ≠ 0 then c1 else c2, s)) →
    P (.ite e c1 c2, s)) ∧
  (∀ s, P (.break, s)) ∧
  (∀ s, P (.continue, s)) ∧
  (∀ (e : ExpHOL width) (c : ProgHOL width) (s : PanSemStateFiniteExact width σ),
    (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
        (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
        (v1 : PanSemResultExact width),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
        (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
        res = some v1 ∧ v1 = .continue →
      P (.while e c, s1)) ∧
    (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
        (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
        (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
        res = none →
      P (.while e c, s1)) ∧
    (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
      @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 →
      P (c, s.decClockHOLFinite)) →
    P (.while e c, s)) ∧
  (∀ (e : ExpHOL width) s, P (.return e, s)) ∧
  (∀ (eid : MlS) (e : ExpHOL width) s, P (.raise eid e, s)) ∧
  (∀ s, P (.tick, s)) ∧
  (∀ (v0 v1 : MlS) s, P (.annot v0 v1, s)) ∧
  (∀ (caltyp : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
      (fname : MlS) (argexps : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ),
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
      P (p, PanSemStateFiniteExact.setVarHOLFinite evar exn { st with locals := s.locals })) ∧
    (∀ (args : List (ValueHOL width))
        (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
      s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address))
          argexps = some args ∧
        PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
        v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
      P (prog, { s.decClockHOLFinite with locals := newlocals })) →
    P (.call caltyp fname argexps, s)) ∧
  (∀ (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
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
      P (prog1, PanSemStateFiniteExact.setVarHOLFinite rt retv { st with locals := s.locals })) ∧
    (∀ (args : List (ValueHOL width))
        (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
      s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address))
          argexps = some args ∧
        PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v2 ∧
        v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
      P (prog, { s.decClockHOLFinite with locals := newlocals })) →
    P (.decCall rt shape fname argexps prog1, s)) ∧
  (∀ (ffi_index : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width) s,
    P (.extCall ffi_index ptr1 len1 ptr2 len2, s))

private theorem lexOfClockLe {a' a b' b : Nat} (ha : a' ≤ a) (hb : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.lt_or_eq_of_le ha with h | rfl
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ hb

private theorem lexOfClockLt {a' a b' b : Nat} (ha : a' < a) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) :=
  Prod.Lex.left _ _ ha

/-- A run from a positive-clock state after `dec_clock` ends below the
    starting clock. -/
private theorem clock_lt_of_decClock_run {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (prog : ProgHOL width) (hclk : s.clock ≠ 0) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState
      { s.decClockHOLFinite with locals := newlocals } prog).2.clock < s.clock := by
  have hle := evaluateHOLFiniteState_clock_le
    { s.decClockHOLFinite with locals := newlocals } prog
  have hc : ({ s.decClockHOLFinite with locals := newlocals } :
      PanSemStateFiniteExact width σ).clock = s.clock - 1 := rfl
  omega

private theorem evaluateIndHOL_go {width : Nat} {σ : Type} [NeZero width]
    (P : ProgHOL width × PanSemStateFiniteExact width σ → Prop) (H : PanEvaluateIndHyps P) :
    ∀ (p : ProgHOL width) (s : PanSemStateFiniteExact width σ), P (p, s)
  | .skip, s => H.1 s
  | .dec v sh e prog, s => H.2.1 v sh e prog s (fun value _ =>
      evaluateIndHOL_go P H prog { s with locals := s.locals.update (v, value) })
  | .assign vk v src, s => H.2.2.1 vk v src s
  | .primitive v pop es, s => H.2.2.2.1 v pop es s
  | .store dst src, s => H.2.2.2.2.1 dst src s
  | .store32 dst src, s => H.2.2.2.2.2.1 dst src s
  | .storeByte dst src, s => H.2.2.2.2.2.2.1 dst src s
  | .shMemLoad op vk v ad, s => H.2.2.2.2.2.2.2.1 op vk v ad s
  | .shMemStore op ad e, s => H.2.2.2.2.2.2.2.2.1 op ad e s
  | .seq c1 c2, s => H.2.2.2.2.2.2.2.2.2.1 c1 c2 s
      ⟨fun res s1 hr => evaluateIndHOL_go P H c2 s1, evaluateIndHOL_go P H c1 s⟩
  | .ite e c1 c2, s => H.2.2.2.2.2.2.2.2.2.2.1 e c1 c2 s (fun v1 v6 w _ =>
      if hw : w ≠ 0 then by
        rw [if_pos hw]; exact evaluateIndHOL_go P H c1 s
      else by
        rw [if_neg hw]; exact evaluateIndHOL_go P H c2 s)
  | .break, s => H.2.2.2.2.2.2.2.2.2.2.2.1 s
  | .continue, s => H.2.2.2.2.2.2.2.2.2.2.2.2.1 s
  | .while e c, s => H.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e c s
      ⟨fun v2 v11 w res s1 v1 hh => evaluateIndHOL_go P H (.while e c) s1,
       fun v2 v11 w res s1 hh => evaluateIndHOL_go P H (.while e c) s1,
       fun v2 v11 w hh => evaluateIndHOL_go P H c s.decClockHOLFinite⟩
  | .return e, s => H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e s
  | .raise eid e, s => H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 eid e s
  | .tick, s => H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s
  | .annot v0 v1, s => H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v0 v1 s
  | .call caltyp fname argexps, s => H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 caltyp fname argexps s
      ⟨fun args v7 prog v12 newlocals return_sh eval_prog v4 st v8 eid exn v v1 v2 v3 eid' v5
          evar p sh hh =>
        evaluateIndHOL_go P H p
          (PanSemStateFiniteExact.setVarHOLFinite evar exn { st with locals := s.locals }),
       fun args v7 prog v12 newlocals return_sh hh =>
        evaluateIndHOL_go P H prog { s.decClockHOLFinite with locals := newlocals }⟩
  | .decCall rt shape fname argexps prog1, s =>
      H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rt shape fname argexps prog1 s
      ⟨fun args v2 prog v7 newlocals return_sh eval_prog v st v3 retv hh =>
        evaluateIndHOL_go P H prog1
          (PanSemStateFiniteExact.setVarHOLFinite rt retv { st with locals := s.locals }),
       fun args v2 prog v7 newlocals return_sh hh =>
        evaluateIndHOL_go P H prog { s.decClockHOLFinite with locals := newlocals }⟩
  | .extCall ffi_index ptr1 len1 ptr2 len2, s =>
      H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ffi_index ptr1 len1 ptr2 len2 s
termination_by p s => (s.clock, sizeOf p)
decreasing_by
  all_goals simp_wf
  -- `Dec` body
  · exact lexOfClockLe (Nat.le_refl _) (by omega)
  -- `Seq` second program at the post-state of the first
  · refine lexOfClockLe ?_ (by omega)
    have hle := evaluateHOLFiniteState_clock_le s c1
    rw [← hr.1] at hle
    exact hle
  -- `Seq` first program
  · exact lexOfClockLe (Nat.le_refl _) (by omega)
  -- `If` branches
  · exact lexOfClockLe (Nat.le_refl _) (by omega)
  · exact lexOfClockLe (Nat.le_refl _) (by omega)
  -- `While` re-entry after `Continue` and after `NONE`
  · apply lexOfClockLt
    have hle := evaluateHOLFiniteState_clock_le s.decClockHOLFinite c
    rw [← hh.2.2.2.2.2.1] at hle
    have := hh.2.2.2.2.1
    simp only [PanSemStateFiniteExact.decClockHOLFinite] at hle
    omega
  · apply lexOfClockLt
    have hle := evaluateHOLFiniteState_clock_le s.decClockHOLFinite c
    rw [← hh.2.2.2.2.2.1] at hle
    have := hh.2.2.2.2.1
    simp only [PanSemStateFiniteExact.decClockHOLFinite] at hle
    omega
  -- `While` body at `dec_clock s`
  · apply lexOfClockLt
    have := hh.2.2.2.2
    simp only [PanSemStateFiniteExact.decClockHOLFinite]
    omega
  -- `Call` handler at the callee post-state, and callee body
  · apply lexOfClockLt
    have hlt := clock_lt_of_decClock_run s newlocals prog hh.2.2.2.2.1
    rw [← hh.2.2.2.2.2.1, hh.2.2.2.2.2.2.1] at hlt
    simpa [PanSemStateFiniteExact.setVarHOLFinite] using hlt
  · apply lexOfClockLt
    have := hh.2.2.2.2
    simp only [PanSemStateFiniteExact.decClockHOLFinite]
    omega
  -- `DecCall` continuation at the callee post-state, and callee body
  · apply lexOfClockLt
    have hlt := clock_lt_of_decClock_run s newlocals prog hh.2.2.2.2.1
    rw [← hh.2.2.2.2.2.1, hh.2.2.2.2.2.2.1] at hlt
    simpa [PanSemStateFiniteExact.setVarHOLFinite] using hlt
  · apply lexOfClockLt
    have := hh.2.2.2.2
    simp only [PanSemStateFiniteExact.decClockHOLFinite]
    omega


/-- Exact port of HOL `panSem$evaluate_ind` (`panSemScript.sml:777-778`, the
    induction theorem of `evaluate` rebound with `fix_clock_evaluate`). The
    predicate `P` is on `(program, state)` pairs, as in HOL. The 21 conjuncts
    are transcribed binder for binder and in HOL order from the checked HOL
    print `scripts/hol-probes/pan_sem_evaluate_ind_probe.out`. `evaluate` is the
    tagged total `evaluateHOLFiniteState` (line-780 `evaluate_def`), `eval s` and
    `OPT_MMAP (eval s)` use the classical address decision of the tagged Pan
    clauses, and `lookup_code`/`dec_clock`/`set_var`/`is_valid_value`/`shape_of`
    are the helpers those clauses use. `s.locals⟨v ↦ value⟩` is
    `s.locals.update (v, value)` (`FUPDATE`), and `FLOOKUP` is `.lookup`. The
    four state maps are the canonical `HolFiniteMapExact` translation, and
    `'a word` is `BitVec width`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_ind" 777
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateIndHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (P : ProgHOL width × PanSemStateFiniteExact width σ → Prop),
      (
      (∀ s, P (.skip, s)) ∧
      (∀ (v : MlS) (sh : ShapeHOL) (e : ExpHOL width) (prog : ProgHOL width)
          (s : PanSemStateFiniteExact width σ),
        (∀ value : ValueHOL width,
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some value ∧
            sh = shapeOfHOLExact value →
          P (prog, { s with locals := s.locals.update (v, value) })) →
        P (.dec v sh e prog, s)) ∧
      (∀ (vk : VarKind) (v : MlS) (src : ExpHOL width) s, P (.assign vk v src, s)) ∧
      (∀ (v : MlS) (pop : PrimOp) (es : List (ExpHOL width)) s, P (.primitive v pop es, s)) ∧
      (∀ (dst src : ExpHOL width) s, P (.store dst src, s)) ∧
      (∀ (dst src : ExpHOL width) s, P (.store32 dst src, s)) ∧
      (∀ (dst src : ExpHOL width) s, P (.storeByte dst src, s)) ∧
      (∀ (op : OpSize) (vk : VarKind) (v : MlS) (ad : ExpHOL width) s,
        P (.shMemLoad op vk v ad, s)) ∧
      (∀ (op : OpSize) (ad e : ExpHOL width) s, P (.shMemStore op ad e, s)) ∧
      (∀ (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ),
        (∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
            (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s c1 ∧ res = none →
            P (c2, s1)) ∧
          P (c1, s) →
        P (.seq c1 c2, s)) ∧
      (∀ (e : ExpHOL width) (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ),
        (∀ (v1 : ValueHOL width) (v6 : HolWordLab width) (w : BitVec width),
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v1 ∧
            v1 = .val v6 ∧ v6 = .word w →
          P (if w ≠ 0 then c1 else c2, s)) →
        P (.ite e c1 c2, s)) ∧
      (∀ s, P (.break, s)) ∧
      (∀ s, P (.continue, s)) ∧
      (∀ (e : ExpHOL width) (c : ProgHOL width) (s : PanSemStateFiniteExact width σ),
        (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
            (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
            (v1 : PanSemResultExact width),
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
            (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
            res = some v1 ∧ v1 = .continue →
          P (.while e c, s1)) ∧
        (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
            (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
            (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
            res = none →
          P (.while e c, s1)) ∧
        (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
          @evalHOLExact width σ _ s.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 →
          P (c, s.decClockHOLFinite)) →
        P (.while e c, s)) ∧
      (∀ (e : ExpHOL width) s, P (.return e, s)) ∧
      (∀ (eid : MlS) (e : ExpHOL width) s, P (.raise eid e, s)) ∧
      (∀ s, P (.tick, s)) ∧
      (∀ (v0 v1 : MlS) s, P (.annot v0 v1, s)) ∧
      (∀ (caltyp : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
          (fname : MlS) (argexps : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ),
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
          P (p, PanSemStateFiniteExact.setVarHOLFinite evar exn { st with locals := s.locals })) ∧
        (∀ (args : List (ValueHOL width))
            (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
            (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
            (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
          s.evalListHOLFinite
              (h := fun address => Classical.propDecidable (s.memaddrs address))
              argexps = some args ∧
            PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
            v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
          P (prog, { s.decClockHOLFinite with locals := newlocals })) →
        P (.call caltyp fname argexps, s)) ∧
      (∀ (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
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
          P (prog1,
            PanSemStateFiniteExact.setVarHOLFinite rt retv { st with locals := s.locals })) ∧
        (∀ (args : List (ValueHOL width))
            (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
            (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
            (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
          s.evalListHOLFinite
              (h := fun address => Classical.propDecidable (s.memaddrs address))
              argexps = some args ∧
            PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v2 ∧
            v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
          P (prog, { s.decClockHOLFinite with locals := newlocals })) →
        P (.decCall rt shape fname argexps prog1, s)) ∧
      (∀ (ffi_index : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width) s,
        P (.extCall ffi_index ptr1 len1 ptr2 len2, s))) →
      ∀ (v : ProgHOL width) (v1 : PanSemStateFiniteExact width σ), P (v, v1) := by
  intro P h v v1
  exact evaluateIndHOL_go P h v v1

end Flapjack
