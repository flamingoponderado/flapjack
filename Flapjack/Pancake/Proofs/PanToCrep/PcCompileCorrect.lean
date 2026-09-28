import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedDecs
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.PanToCrep.CompileExact

/-!
# The `pc_compile_correct` statement over the exact carriers

HOL `pc_compile_correct` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`)
is proved by `recInduct panSemTheory.evaluate_ind`, whose predicate is
`P (v, v1)`: for every `res s1 t ctxt`, the source run
`evaluate (v, v1) = (res, s1)` plus the pre-state relations imply a target run of
`compile ctxt v` with the post-state relations and the result correspondence.

`pcCompileCorrectAt program source` is that predicate over the faithful
carriers:

* the source run is the tagged total `evaluateHOLFiniteState` (the line-780
  `panSem$evaluate_def`, `evaluateHOLFiniteState_eq_evaluate_def`);
* the target run is the tagged total `evalCrepSemHOLProgExact` (the line-443
  `crepSem$evaluate_def`, `evalCrepSemHOLProgExact_eq_evaluate_def`);
* the compiler is the tagged `compileProgExactHOLW` (`compile_def`);
* `state_rel`, `code_rel`, `excp_rel`, and `locals_rel` are the tagged exact
  relations, `globals_lookup` is `globalsLookupHOL`, and `localised_prog` is
  `localisedProgHOL`.

Every hypothesis and conclusion conjunct follows HOL's order. The target run is
existentially quantified, as in HOL. No target result, target post-state, or
post-state relation is assumed. The HOL theorem is
`∀ program source, pcCompileCorrectAt program source`. Its constructor cases
are proved against this predicate with the IHs of HOL's rebound `evaluate_ind`
(`panSemScript.sml:777-778`).

This definition is Flapjack infrastructure: it is the body of the HOL theorem,
not a separate HOL declaration, so it carries no `@[hol]` tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL sizeOfShapeHOL)

/-- The `case res of ...` result conjunct of HOL `pc_compile_correct`
    (`pan_to_crepProofScript.sml:452-467`), relating the source result `res`
    to the target result `res1`, with `s1`/`t1` the post-states. -/
def pcCompileCorrectResultRel {width : Nat} {σ : Type} [NeZero width]
    (context : PanToCrepContextExact width)
    (s1 : PanSemStateFiniteExact width σ) (t1 : CrepSemHOLState width σ) :
    Option (PanSemResultExact width) → Option (CrepResultHOLExact width) → Prop
  | none, res1 => res1 = none ∧ panToCrepLocalsRelFiniteExact context s1.locals t1.locals
  | some .error, _ => False
  | some .timeOut, res1 => res1 = some .timeOut
  | some .break, res1 =>
      res1 = some (.break 0) ∧ panToCrepLocalsRelFiniteExact context s1.locals t1.locals
  | some .continue, res1 =>
      res1 = some (.continue 0) ∧ panToCrepLocalsRelFiniteExact context s1.locals t1.locals
  | some (.returned v), res1 => res1 = some (.return (flattenHOL v))
  | some (.exception eid v'), res1 =>
      match context.eids.lookup eid with
      | none => False
      | some n =>
          res1 = some (.exception n) ∧
            (1 ≤ sizeOfShapeHOL (shapeOfHOLExact v') →
              globalsLookupHOL t1 v' = some (flattenHOL v') ∧
                sizeOfShapeHOL (shapeOfHOLExact v') ≤ 32)
  | some (.finalFfi f), res1 => res1 = some (.finalFfi f)

/-- HOL `pc_compile_correct`'s induction predicate `P (v, v1)`
    (`pan_to_crepProofScript.sml:442-468`) over the exact carriers; see the
    module note. -/
def pcCompileCorrectAt {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (source : PanSemStateFiniteExact width σ) : Prop :=
  ∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width),
    source.evaluateHOLFiniteState program = (res, s1) →
    res ≠ some .error →
    panToCrepStateRelFiniteExact source t →
    codeRelExactHOLW ctxt source.code t.code →
    panToCrepExcpRelFiniteExact ctxt.eids source.eshapes →
    panToCrepLocalsRelFiniteExact ctxt source.locals t.locals →
    localisedProgHOL program = true →
    ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt program) = (res1, t1) ∧
      panToCrepStateRelFiniteExact s1 t1 ∧
      codeRelExactHOLW ctxt s1.code t1.code ∧
      panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
      pcCompileCorrectResultRel ctxt s1 t1 res res1

/-- The two induction hypotheses of the `Call caltyp fname argexps` case of HOL
    `panSem$evaluate_ind`, as rebound at `panSemScript.sml:777-778`
    (`REWRITE_RULE [fix_clock_evaluate] evaluate_ind`), instantiated at
    `pcCompileCorrectAt`. The first IH is for a caught exception's handler
    body `p`, run on `set_var evar exn (st with locals := s.locals)`. The second
    is for the callee body, run on `dec_clock s with locals := newlocals`. The
    side conditions are HOL's, over the same exact helpers as the tagged Call
    arm of `evaluateHOLFiniteState_eq_evaluate_def`. HOL's `eid = eid'` equation
    is substituted into the handler triple. -/
def pcCompileCorrectCallIH {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (source : PanSemStateFiniteExact width σ) : Prop :=
  (∀ (values : List (ValueHOL width)) (prog : ProgHOL width)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
      (st : PanSemStateFiniteExact width σ) (eid : MlS) (exn : ValueHOL width)
      (v1 : Option (VarKind × MlS)) (evar : MlS) (p : ProgHOL width) (sh : ShapeHOL),
    source.evalListHOLFinite
        (h := fun address => Classical.propDecidable (source.memaddrs address))
        arguments = some values →
    PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function values =
      some (prog, newlocals, returnShape) →
    source.clock ≠ 0 →
    (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals).evaluateHOLFiniteState
        prog = (some (.exception eid exn), st) →
    info = some (v1, some (eid, evar, p)) →
    source.eshapes.lookup eid = some sh →
    shapeOfHOLExact exn = sh →
    isValidValueHOLExact source.toExact .local evar exn = true →
    pcCompileCorrectAt p
      (PanSemStateFiniteExact.setVarHOLFinite evar exn { st with locals := source.locals })) ∧
  (∀ (values : List (ValueHOL width)) (prog : ProgHOL width)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
    source.evalListHOLFinite
        (h := fun address => Classical.propDecidable (source.memaddrs address))
        arguments = some values →
    PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function values =
      some (prog, newlocals, returnShape) →
    source.clock ≠ 0 →
    pcCompileCorrectAt prog (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals))

/-- The `Skip` case of HOL `pc_compile_correct` (`pan_to_crepProofScript.sml:493-497`)
    against `pcCompileCorrectAt`. It checks that the predicate can be discharged
    from the tagged clause equations alone: source `Skip` returns `(NONE, s)`,
    `compile ctxt Skip = Skip`, and target `Skip` returns `(NONE, t)`. Untagged:
    it is one case of the theorem, and the assembled theorem is not yet proved. -/
theorem pcCompileCorrectAt_skip {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.skip : ProgHOL width) source := by
  intro res s1 t ctxt hrun _ hstate hcode hexcp hlocals _
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_skip] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  refine ⟨none, t, ?_, hstate, hcode, hexcp, rfl, hlocals⟩
  simpa [compileProgExactHOLW] using evalCrepSemHOLProgExact_skip t

end Flapjack
