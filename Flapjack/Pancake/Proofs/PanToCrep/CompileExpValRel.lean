import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Semantics.PanSem.EvalFinite
import Flapjack.Pancake.Semantics.PanProps.LocalisedExpSimps

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

/-- Faithful `Var Global` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:166-168`). The HOL proof
    is `fs[localised_exp_simps]`: a global variable is not localised, so the
    `localised_exp e` premise is contradictory and the case is vacuous. -/
theorem compileExpValRelHOL_var_global {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (name : MlS) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (_heval : state.evalHOLFinite (ExpHOL.var .global name) = some value)
    (hlocalised : localisedExpHOL (width := width) (ExpHOL.var .global name) = true)
    (_hcompile : compileExpExactHOLW context (ExpHOL.var .global name) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  simp only [localisedExpHOL, everyExpHOL] at hlocalised
  exact (Bool.false_ne_true hlocalised).elim

/-- List-level companion of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:171-198`) used by the
    `RStruct` case. Given the per-member statement — the shape of the
    `eval_ind` induction hypotheses for the sub-expressions — it proves the
    compiled flat-map evaluates to `flatten (RStruct values)`, with matching
    output length, output shape, and shape well-formedness. -/
theorem compileExpListValRelHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [ht : DecidablePred targetState.memaddrs]
    (fields : List (ExpHOL width))
    (hrel : ∀ (expression : ExpHOL width), expression ∈ fields →
        (value : ValueHOL width) → (expressions : List (CrepExpHOL width)) →
        (shape : ShapeHOL) →
        state.evalHOLFinite expression = some value →
        localisedExpHOL expression = true →
        compileExpExactHOLW context expression = (expressions, shape) →
        expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
        expressions.length = sizeOfShapeHOL shape ∧
        shapeOfHOLExact value = shape ∧
        isWfShapeExactHOL ([] : StructContextExact) shape = true)
    : ∀ (values : List (ValueHOL width))
        (compiled : List (List (CrepExpHOL width) × ShapeHOL)),
      state.evalListHOLFinite fields = some values →
      everyExpListHOL (width := width) localisedExpPredHOL fields = true →
      compileExpExactHOLWList context fields = compiled →
      (compiled.flatMap Prod.fst).map (evalCrepSemHOLExp targetState) =
          (flattenHOL (ValueHOL.rStruct values)).map some ∧
        (compiled.flatMap Prod.fst).length =
          sizeOfShapeHOL (.comb (compiled.map Prod.snd)) ∧
        shapeOfHOLExact (ValueHOL.rStruct values) = .comb (compiled.map Prod.snd) ∧
        isWfShapeExactHOL ([] : StructContextExact) (.comb (compiled.map Prod.snd)) =
          true := by
  induction fields with
  | nil =>
      intro values compiled heval hlocalised hcompile
      obtain rfl : values = [] := by
        simpa only [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact,
          evalListHOLExact, Option.some.injEq] using heval.symm
      obtain rfl : compiled = [] := by
        simpa only [compileExpExactHOLWList] using hcompile.symm
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [flattenHOL, shapeOfHOLExact, sizeOfShapeHOL, isWfShapeExactHOL]
  | cons head tail ih =>
      intro values compiled heval hlocalised hcompile
      have hdec : everyExpListHOL (width := width) localisedExpPredHOL (head :: tail) =
          (everyExpHOL localisedExpPredHOL head &&
            everyExpListHOL (width := width) localisedExpPredHOL tail) := rfl
      rw [hdec, Bool.and_eq_true] at hlocalised
      obtain ⟨hlocHead, hlocTail⟩ := hlocalised
      have hlocHead' : localisedExpHOL head = true := hlocHead
      rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact,
        evalListHOLExact] at heval
      rw [compileExpExactHOLWList] at hcompile
      cases hh : evalHOLExact state.toExact head with
      | none => simp [hh] at heval
      | some headValue =>
          cases ht : evalListHOLExact state.toExact tail with
          | none => simp [hh, ht] at heval
          | some tailValues =>
              simp only [hh, ht, Option.some.injEq] at heval
              have hevalHead : state.evalHOLFinite head = some headValue := by
                rw [PanSemStateFiniteExact.evalHOLFinite_eq_toExact]; exact hh
              have hevalTail : state.evalListHOLFinite tail = some tailValues := by
                rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact]; exact ht
              cases hhead : compileExpExactHOLW context head with
              | mk headEs headShape =>
                  rw [hhead] at hcompile
                  have hcompiled : compiled =
                      (headEs, headShape) :: compileExpExactHOLWList context tail :=
                    hcompile.symm
                  have hheadRel :=
                    hrel head (by simp) headValue headEs headShape
                      hevalHead hlocHead' hhead
                  have htailRel :
                      ∀ (expression : ExpHOL width), expression ∈ tail →
                        (value : ValueHOL width) → (expressions : List (CrepExpHOL width)) →
                        (shape : ShapeHOL) →
                        state.evalHOLFinite expression = some value →
                        localisedExpHOL expression = true →
                        compileExpExactHOLW context expression = (expressions, shape) →
                        expressions.map (evalCrepSemHOLExp targetState) =
                            (flattenHOL value).map some ∧
                          expressions.length = sizeOfShapeHOL shape ∧
                          shapeOfHOLExact value = shape ∧
                          isWfShapeExactHOL ([] : StructContextExact) shape = true :=
                    fun expression hmem => hrel expression (List.mem_cons_of_mem head hmem)
                  have htail :=
                    ih htailRel tailValues (compileExpExactHOLWList context tail)
                      hevalTail hlocTail rfl
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · rw [hcompiled, List.flatMap_cons, List.map_append, hheadRel.1, htail.1,
                      ← heval]
                    simp only [flattenHOL, List.map_cons, List.flatten_cons, List.map_append]
                  · rw [hcompiled, List.flatMap_cons, List.length_append, hheadRel.2.1,
                      htail.2.1]
                    simp only [sizeOfShapeHOL_comb, sizeOfShapesHOL_cons, List.map_cons]
                  · have htailShapes : tailValues.map shapeOfHOLExact =
                        (compileExpExactHOLWList context tail).map Prod.snd := by
                      have h := htail.2.2.1
                      simp only [shapeOfHOLExact] at h
                      exact ShapeHOL.comb.inj h
                    have houter : shapeOfHOLExact (ValueHOL.rStruct (headValue :: tailValues)) =
                        ShapeHOL.comb (shapeOfHOLExact headValue ::
                          tailValues.map shapeOfHOLExact) := by
                      simp only [shapeOfHOLExact, List.map_cons]
                    rw [hcompiled, ← heval, houter, hheadRel.2.2.1, htailShapes]
                    simp only [List.map_cons]
                  · have htailWf : isWfShapesExactHOL ([] : StructContextExact)
                        ((compileExpExactHOLWList context tail).map Prod.snd) = true := by
                      simpa only [isWfShapeExactHOL_comb] using htail.2.2.2
                    have hwfouter : isWfShapeExactHOL ([] : StructContextExact)
                        (ShapeHOL.comb (headShape ::
                          (compileExpExactHOLWList context tail).map Prod.snd)) =
                        (isWfShapeExactHOL ([] : StructContextExact) headShape &&
                          isWfShapesExactHOL ([] : StructContextExact)
                            ((compileExpExactHOLWList context tail).map Prod.snd)) := by
                      simp only [isWfShapeExactHOL_comb, isWfShapesExactHOL_cons]
                    rw [hcompiled]
                    simp only [List.map_cons]
                    rw [hwfouter, hheadRel.2.2.2, htailWf]
                    rfl

/-- Exact `RStruct` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:171-198`). The HOL proof
    inducts over the sub-expression list with the per-element `eval_ind`
    hypotheses; here that induction hypothesis family is the `hrel` premise and
    the body is delegated to `compileExpListValRelHOL`. -/
theorem compileExpValRelHOL_rstruct {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (fields : List (ExpHOL width)) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hrel : ∀ (expression : ExpHOL width), expression ∈ fields →
        (value : ValueHOL width) → (expressions : List (CrepExpHOL width)) →
        (shape : ShapeHOL) →
        state.evalHOLFinite expression = some value →
        localisedExpHOL expression = true →
        compileExpExactHOLW context expression = (expressions, shape) →
        expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
        expressions.length = sizeOfShapeHOL shape ∧
        shapeOfHOLExact value = shape ∧
        isWfShapeExactHOL ([] : StructContextExact) shape = true)
    (heval : state.evalHOLFinite (.rstruct fields) = some value)
    (hlocalised : localisedExpHOL (.rstruct fields) = true)
    (hcompile : compileExpExactHOLW context (.rstruct fields) = (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  simp only [PanSemStateFiniteExact.evalHOLFinite_rstruct] at heval
  cases hlist : state.evalListHOLFinite fields with
  | none =>
      simp only [hlist, Option.map_none] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some values =>
      simp only [hlist, Option.map_some, Option.some.injEq] at heval
      have hloc : everyExpListHOL (width := width) localisedExpPredHOL fields = true :=
        hlocalised
      have hcompiled := hcompile
      simp only [compileExpExactHOLW] at hcompiled
      obtain ⟨hExpr, hShape⟩ := Prod.mk.inj hcompiled
      have hmain := compileExpListValRelHOL state context targetState fields hrel values
        (compileExpExactHOLWList context fields) hlist hloc rfl
      rw [← heval, ← hExpr, ← hShape]
      exact hmain

/-- Exact `BaseAddr` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-396`, the catch-all
    `eval_def`/`compile_exp_def` case): `eval` returns the state's base address
    as a word and the compiler emits the `BaseAddr` expression, whose Crep
    evaluation returns the target's base address; `state_rel` equates them. -/
theorem compileExpValRelHOL_baseAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite .baseAddr = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcompile : compileExpExactHOLW context .baseAddr = (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hval : value = .val (.word state.baseAddr) := by
    have h := heval
    simp only [PanSemStateFiniteExact.evalHOLFinite_baseAddr] at h
    exact (Option.some.inj h).symm
  have hcomp := hcompile
  simp only [compileExpExactHOLW] at hcomp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcomp
  subst hval
  have haddr : targetState.baseAddr = state.baseAddr :=
    hstate.2.2.2.2.2.2.2.2.1.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [evalCrepSemHOLExp, flattenHOL, haddr]
  · simp [sizeOfShapeHOL]
  · simp [shapeOfHOLExact]
  · simp [isWfShapeExactHOL]

/-- Exact `TopAddr` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-396`, the catch-all
    `eval_def`/`compile_exp_def` case): the `TopAddr` counterpart of
    `compileExpValRelHOL_baseAddr`. -/
theorem compileExpValRelHOL_topAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite .topAddr = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcompile : compileExpExactHOLW context .topAddr = (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hval : value = .val (.word state.topAddr) := by
    have h := heval
    simp only [PanSemStateFiniteExact.evalHOLFinite_topAddr] at h
    exact (Option.some.inj h).symm
  have hcomp := hcompile
  simp only [compileExpExactHOLW] at hcomp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcomp
  subst hval
  have haddr : targetState.topAddr = state.topAddr :=
    hstate.2.2.2.2.2.2.2.2.2.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [evalCrepSemHOLExp, flattenHOL, haddr]
  · simp [sizeOfShapeHOL]
  · simp [shapeOfHOLExact]
  · simp [isWfShapeExactHOL]

/-- Exact `BytesInWord` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-396`, the catch-all
    case): `eval` returns `bytesInWord` and the compiler emits the matching
    `Const`; the Crep side returns the same word. -/
theorem compileExpValRelHOL_bytesInWord {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite .bytesInWord = some value)
    (hcompile : compileExpExactHOLW context .bytesInWord = (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hval : value = .val (.word (bytesInWordHOL width)) := by
    have h := heval
    simp only [PanSemStateFiniteExact.evalHOLFinite_bytesInWord] at h
    exact (Option.some.inj h).symm
  have hcomp := hcompile
  simp only [compileExpExactHOLW] at hcomp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcomp
  subst hval
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [evalCrepSemHOLExp, flattenHOL, bytesInWordHOL]
  · simp [sizeOfShapeHOL]
  · simp [shapeOfHOLExact]
  · simp [isWfShapeExactHOL]

end Flapjack
