import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Semantics.PanSem.EvalFinite

/-!
Exact-carrier statement of HOL `compile_exp_val_rel`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-140`) plus a first,
kernel-checked constructor case.

HOL quantifies over the width-polymorphic source `panSem$state`, source
expression `e`, source value `v`, target `crepSem$state`, compiler context and
compiled expression/shape pair. Its premises are a successful source
evaluation, `state_rel`, `code_rel`, `locals_rel`, `localised_exp`, and the exact
`compile_exp` result; its conclusions are that the compiled expressions evaluate
on the target to `MAP SOME (flatten v)`, with matching output length, output
shape, and shape well-formedness.

This module preserves that shape over the exact carriers `ExpHOL width`,
`ValueHOL width`, `ShapeHOL`, `CrepExpHOL width`, `PanSemStateFiniteExact`,
`CrepSemHOLState`, and `PanToCrepContextExact`, with the exact finite-support
source evaluator `evalHOLFinite` and target evaluator `evalCrepSemHOLExp`.

The full theorem is tracked by `flapjack-4ac.5.81`; this slice records the exact
statement and proves its `Const` case. It is Flapjack proof infrastructure: HOL
proves the cases inside `pc_compile_correct` and does not export a standalone
`compile_exp_val_rel` case, so nothing here carries an `@[hol]` tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact-carrier rendering of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130`). Every premise and
    all four conclusions are preserved over the exact MlString/`word_lab`
    carriers; the source relation `state_rel` is the exact
    `panToCrepStateRelFiniteExact`, `code_rel`/`locals_rel` are the exact
    `codeRelExactHOLW`/`panToCrepLocalsRelFiniteExact`, and `localised_exp` is
    `localisedExpHOL`.

    This is the target of the full port (`flapjack-4ac.5.81`); the constructor
    case below does not complete it. -/
def compileExpValRelHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ)
    [DecidablePred state.memaddrs] [DecidablePred targetState.memaddrs] : Prop :=
  ∀ (expression : ExpHOL width) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL),
    state.evalHOLFinite expression = some value →
    panToCrepStateRelFiniteExact state targetState →
    codeRelExactHOLW context state.code targetState.code →
    panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
    localisedExpHOL expression = true →
    compileExpExactHOLW context expression = (expressions, shape) →
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true

/-- Faithful `Const` constructor case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:143-150`). The premises
    are exactly the HOL case's successful source evaluation and `compile_exp`
    result for `Const w`; the state/code/locals/localisation premises of the
    enclosing theorem are irrelevant to this case and are therefore not
    repeated here. All four HOL conclusions are proved over the exact carriers
    with no target-evaluation premise and no RISC-V-only invariant. -/
theorem compileExpValRelHOL_const {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [ht : DecidablePred targetState.memaddrs]
    (word : BitVec width) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite (ExpHOL.const word) = some value)
    (hcompile : compileExpExactHOLW context (ExpHOL.const word) = (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hval : value = ValueHOL.val (HolWordLab.word word) := by
    have h := heval
    rw [PanSemStateFiniteExact.evalHOLFinite_const] at h
    exact (Option.some.inj h).symm
  have hcomp := hcompile
  simp only [compileExpExactHOLW] at hcomp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcomp
  subst hval
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [evalCrepSemHOLExp, flattenHOL, shapeOfHOLExact, sizeOfShapeHOL,
      isWfShapeExactHOL]

/-- Equation for the target evaluator on a local variable, matching the `Var`
    clause of `crepSemScript.sml:90-137`. -/
private theorem evalCrepSemHOLExp_var {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs] (name : Nat) :
    evalCrepSemHOLExp state (.var name) = state.locals.lookup name := by
  simp only [evalCrepSemHOLExp]

/-- Faithful `Var Local` constructor case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:151-165`). The premises
    are exactly the HOL case's successful source evaluation, `locals_rel`, and
    `compile_exp` result; the target code/state relation and localisation
    premises are irrelevant to this case and are not repeated. All four HOL
    conclusions are proved over the exact carriers with no target-evaluation
    premise and no RISC-V-only invariant. -/
theorem compileExpValRelHOL_var_local {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [ht : DecidablePred targetState.memaddrs]
    (name : MlS) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite (ExpHOL.var .local name) = some value)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (ExpHOL.var .local name) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hval : state.locals.lookup name = some value := by
    simpa only [PanSemStateFiniteExact.evalHOLFinite_var_local] using heval
  obtain ⟨slots, hcontext, hslotsLen, hmapM, hwf⟩ :=
    panToCrepLocalsRelLookupCtxtFiniteExact context state.locals targetState.locals
      name value hlocals hval
  have hcomp := hcompile
  simp only [compileExpExactHOLW] at hcomp
  rw [hcontext] at hcomp
  dsimp only at hcomp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcomp
  have hmap : slots.map targetState.locals.lookup = (flattenHOL value).map some :=
    (optMmapEqSome slots targetState.locals.lookup (flattenHOL value)).mp hmapM
  have hfun : (evalCrepSemHOLExp targetState ∘ CrepExpHOL.var) =
      targetState.locals.lookup :=
    funext (fun n => evalCrepSemHOLExp_var targetState n)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.map_map, hfun]
    exact hmap
  · rw [List.length_map, hslotsLen, flattenHOL_length_eq_sizeOfShapeHOL value hwf]
  · rfl
  · exact hwf

end Flapjack
