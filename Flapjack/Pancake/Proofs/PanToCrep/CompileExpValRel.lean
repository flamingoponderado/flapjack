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
proves the cases inside `compile_exp_val_rel` and does not export a standalone
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

/-- `cexpHeads` over a list of singleton lists. -/
private theorem cexpHeads_map_singleton {β : Type} (l : List β) :
    cexpHeads (l.map (fun b => [b])) = some l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, cexpHeads, ih]

/-- `cexpHeads` prepends a singleton head. -/
private theorem cexpHeads_cons_singleton {β : Type} (b : β) (l : List (List β))
    (heads : List β) (h : cexpHeads l = some heads) :
    cexpHeads ([b] :: l) = some (b :: heads) := by
  simp only [cexpHeads]
  rw [h]

/-- A word-valued exact value is `Val (Word w)` for some word `w`. -/
private theorem valueIsWord_eq_true_iff {width : Nat} [NeZero width] (value : ValueHOL width) :
    valueIsWord value = true ↔ ∃ word, value = ValueHOL.val (HolWordLab.word word) := by
  cases value with
  | val lab => cases lab with
    | word word => simp [valueIsWord]
  | rStruct fields => simp [valueIsWord]
  | nStruct name fields => simp [valueIsWord]

/-- List-level heads correspondence used by the `Op`/`Panop` cases of HOL
    `compile_exp_val_rel` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml`).
    Given the per-member statement (the `eval_ind` induction hypothesis family)
    and a successful, all-word `evalListHOLFinite`, the `cexpHeads` of the
    compiled first components evaluates elementwise to the words of the source
    values. Untagged Flapjack-specific infrastructure. -/
theorem cexpHeads_compileExpListValRelHOL {width : Nat} {σ : Type} [NeZero width]
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
      values.all valueIsWord = true →
      compileExpExactHOLWList context fields = compiled →
      ∃ heads : List (CrepExpHOL width),
        cexpHeads (compiled.map Prod.fst) = some heads ∧
        heads.mapM (evalCrepSemHOLExp targetState) =
          some (values.map (fun value => HolWordLab.word (valueWord value))) := by
  induction fields with
  | nil =>
      intro values compiled heval _hevery hall hcompile
      obtain rfl : values = [] := by
        simpa only [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact, evalListHOLExact,
          Option.some.injEq] using heval.symm
      obtain rfl : compiled = [] := by
        simpa only [compileExpExactHOLWList] using hcompile.symm
      exact ⟨[], by simp only [List.map_nil, cexpHeads], by simp [List.mapM_nil]⟩
  | cons head tail ih =>
      intro values compiled heval hevery hall hcompile
      have hdec : everyExpListHOL (width := width) localisedExpPredHOL (head :: tail) =
          (everyExpHOL localisedExpPredHOL head &&
            everyExpListHOL (width := width) localisedExpPredHOL tail) := rfl
      rw [hdec, Bool.and_eq_true] at hevery
      obtain ⟨hlocHead, hlocTail⟩ := hevery
      have hlocHead' : localisedExpHOL head = true := hlocHead
      rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact, evalListHOLExact] at heval
      rw [compileExpExactHOLWList] at hcompile
      cases hh : evalHOLExact state.toExact head with
      | none => simp [hh] at heval
      | some headValue =>
          cases ht' : evalListHOLExact state.toExact tail with
          | none => simp [hh, ht'] at heval
          | some tailValues =>
              have hvalues : headValue :: tailValues = values := by
                simpa only [hh, ht', Option.some.injEq] using heval
              rw [← hvalues] at hall
              simp only [List.all_cons, Bool.and_eq_true] at hall
              obtain ⟨hheadWord, htailWord⟩ := hall
              obtain ⟨word, rfl⟩ := (valueIsWord_eq_true_iff headValue).mp hheadWord
              have hevalHead : state.evalHOLFinite head = some (.val (.word word)) := by
                rw [PanSemStateFiniteExact.evalHOLFinite_eq_toExact]; exact hh
              have hevalTail : state.evalListHOLFinite tail = some tailValues := by
                rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact]; exact ht'
              cases hhead : compileExpExactHOLW context head with
              | mk headEs headShape =>
                  rw [hhead] at hcompile
                  have hcompiled : compiled =
                      (headEs, headShape) :: compileExpExactHOLWList context tail :=
                    hcompile.symm
                  have hheadRel :=
                    hrel head (by simp) (.val (.word word)) headEs headShape
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
                  obtain ⟨headsTail, hcexpTail, hmapTail⟩ :=
                    ih htailRel tailValues (compileExpExactHOLWList context tail)
                      hevalTail hlocTail htailWord rfl
                  have hheadMap : headEs.map (evalCrepSemHOLExp targetState) =
                      [some (.word word)] := by
                    rw [hheadRel.1]
                    simp only [flattenHOL, List.map_cons, List.map_nil]
                  have hlen1 : headEs.length = 1 := by
                    have h := congrArg List.length hheadMap
                    simpa only [List.length_map, List.length_cons, List.length_nil] using h
                  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen1
                  subst hx
                  have hxEval : evalCrepSemHOLExp targetState x = some (.word word) := by
                    have h := hheadMap
                    rw [List.map_cons, List.map_nil] at h
                    exact (List.cons.inj h).1
                  refine ⟨x :: headsTail, ?_, ?_⟩
                  · rw [hcompiled]
                    rw [show List.map Prod.fst (([x], headShape) :: compileExpExactHOLWList context tail) =
                          [x] :: List.map Prod.fst (compileExpExactHOLWList context tail) from rfl]
                    exact cexpHeads_cons_singleton x _ headsTail hcexpTail
                  · rw [List.mapM_cons]
                    rw [hxEval, hmapTail, ← hvalues]
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

/-- Flapjack-specific staged constructor lemma for the `BaseAddr` leaf of the
    exact `compile_exp_val_rel` induction
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-396`, the catch-all
    `eval_def`/`compile_exp_def` case). It is not a standalone HOL declaration:
    the HOL theorem's `localised_exp`, `code_rel` and `locals_rel` hypotheses
    are unnecessary in this leaf proof (only `state_rel` is used, to equate the
    base addresses), so the statement keeps just `state_rel`; the full
    `compile_exp_val_rel` theorem remains open (bead flapjack-4ac.5.81). -/
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

/-- Flapjack-specific staged constructor lemma for the `TopAddr` leaf of the
    exact `compile_exp_val_rel` induction
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-396`, the catch-all
    `eval_def`/`compile_exp_def` case), the `TopAddr` counterpart of
    `compileExpValRelHOL_baseAddr`. It is not a standalone HOL declaration: the
    HOL theorem's `localised_exp`, `code_rel` and `locals_rel` hypotheses are
    unnecessary in this leaf proof (only `state_rel` is used, to equate the top
    addresses); the full `compile_exp_val_rel` theorem remains open (bead
    flapjack-4ac.5.81). -/
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

/-- Flapjack-specific staged constructor lemma for the `BytesInWord` leaf of
    the exact `compile_exp_val_rel` induction
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-396`, the catch-all
    case): `eval` returns `bytesInWord` and the compiler emits the matching
    `Const`; the Crep side returns the same word. It is not a standalone HOL
    declaration: the HOL theorem's `localised_exp`, `code_rel`, `locals_rel`
    (and even `state_rel`) hypotheses are unnecessary here because the witness
    is the constant `bytesInWord` on both sides; the full
    `compile_exp_val_rel` theorem remains open (bead flapjack-4ac.5.81). -/
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

/-- Flapjack-specific staged constructor lemma for the `NStruct` leaf of the
    exact `compile_exp_val_rel` induction
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-396`, the catch-all
    case). It is not a standalone HOL declaration: the leaf is vacuous because
    the exact `state_rel` forces the source structure context to be empty, so
    `structContextLookupHOL` (and hence `eval`) always fails. -/
theorem compileExpValRelHOL_nstruct {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (name : MlS) (fields : List (MlS × ExpHOL width))
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite (.nstruct name fields) = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (_hcompile : compileExpExactHOLW context (.nstruct name fields) = (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hstructs := panToCrepStateRelFiniteExact_structs state targetState hstate
  rw [PanSemStateFiniteExact.evalHOLFinite_nstruct, hstructs] at heval
  simp only [structContextLookupHOL] at heval
  exact absurd heval.symm (Option.some_ne_none value)

/-- Flapjack-specific staged constructor lemma for the `NField` leaf of the
    exact `compile_exp_val_rel` induction
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130-396`, the catch-all
    case). It is not a standalone HOL declaration: the leaf is vacuous because
    the exact `state_rel` forces the source structure context to be empty, so
    the structure lookup guard in `eval` always fails. -/
theorem compileExpValRelHOL_nfield {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (name : MlS) (value' : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite (.nfield name value') = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (_hcompile : compileExpExactHOLW context (.nfield name value') = (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hstructs := panToCrepStateRelFiniteExact_structs state targetState hstate
  rw [PanSemStateFiniteExact.evalHOLFinite_nfield, hstructs] at heval
  cases hval : state.evalHOLFinite value' with
  | none =>
      simp only [hval] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some inner =>
      cases inner <;>
        simp only [hval, structContextLookupHOL, Option.isSome_none,
          Bool.false_eq_true, if_false] at heval <;>
        exact absurd heval.symm (Option.some_ne_none value)

/-! ### `compFieldHOL` slice correspondence

The exact `RField` leaf of `compile_exp_val_rel` needs the correspondence
between the compiled sub-expression list (whose evaluation is the flattened
value list covered by `compileExpListValRelHOL`) and `compFieldHOL`, which
consumes `sizeOfShapeHOL` expressions per taken field.  `compFieldHOL_slice`
records that correspondence for every list index. -/

private theorem compFieldHOL_slice
    {width : Nat} {σ : Type} [NeZero width]
    (targetState : CrepSemHOLState width σ) [DecidablePred targetState.memaddrs]
    (values : List (ValueHOL width)) (cexp : List (CrepExpHOL width))
    (hEval : cexp.map (evalCrepSemHOLExp targetState)
      = (flattenHOL (.rStruct values)).map some)
    (hvalues : isWfShapesExactHOL ([] : StructContextExact) (values.map shapeOfHOLExact) = true) :
    ∀ (index : Nat) (value : ValueHOL width), values[index]? = some value →
      (compFieldHOL index (values.map shapeOfHOLExact) cexp).1.map
          (evalCrepSemHOLExp targetState) = (flattenHOL value).map some
      ∧ (compFieldHOL index (values.map shapeOfHOLExact) cexp).2 = shapeOfHOLExact value
      ∧ (compFieldHOL index (values.map shapeOfHOLExact) cexp).1.length
          = sizeOfShapeHOL (shapeOfHOLExact value)
      ∧ isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
  induction values generalizing cexp with
  | nil =>
      intro index value hget
      simp at hget
  | cons v rest ih =>
      intro index value hget
      have hWfHead : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact v) = true := by
        have h := hvalues
        simp only [List.map_cons, isWfShapesExactHOL_cons, Bool.and_eq_true] at h
        exact h.1
      have hWfRest :
          isWfShapesExactHOL ([] : StructContextExact) (rest.map shapeOfHOLExact) = true := by
        have h := hvalues
        simp only [List.map_cons, isWfShapesExactHOL_cons, Bool.and_eq_true] at h
        exact h.2
      have hsizeHead : (flattenHOL v).length = sizeOfShapeHOL (shapeOfHOLExact v) :=
        flattenHOL_length_eq_sizeOfShapeHOL v hWfHead
      have hmapSomeLen :
          (List.map some (flattenHOL v)).length = sizeOfShapeHOL (shapeOfHOLExact v) := by
        simpa only [List.length_map] using hsizeHead
      have hEvalSplit : cexp.map (evalCrepSemHOLExp targetState)
          = (flattenHOL v).map some
            ++ (flattenHOL (.rStruct rest)).map some := by
        rw [hEval]
        simp only [flattenHOL, List.map_cons, List.flatten_cons, List.map_append]
      have hlenCexp : cexp.length = (flattenHOL (.rStruct (v :: rest))).length := by
        have h := congrArg List.length hEval
        simpa only [List.length_map] using h
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          have htake : (cexp.take (sizeOfShapeHOL (shapeOfHOLExact v))).map
              (evalCrepSemHOLExp targetState) = (flattenHOL v).map some := by
            rw [List.map_take, hEvalSplit, ← hmapSomeLen, List.take_left]
          have hbound : sizeOfShapeHOL (shapeOfHOLExact v) ≤ cexp.length := by
            rw [hlenCexp, ← hsizeHead]
            simp only [flattenHOL, List.map_cons, List.flatten_cons, List.length_append]
            omega
          refine ⟨?_, ?_, ?_, hWfHead⟩
          · simp only [List.map_cons, compFieldHOL]
            rw [if_true]
            exact htake
          · simp only [List.map_cons, compFieldHOL]
            rw [if_true]
          · simp only [List.map_cons, compFieldHOL]
            rw [if_true]
            rw [List.length_take, Nat.min_eq_left hbound]
      | succ k =>
          simp only [List.getElem?_cons_succ] at hget
          have hdrop : (cexp.drop (sizeOfShapeHOL (shapeOfHOLExact v))).map
              (evalCrepSemHOLExp targetState) = (flattenHOL (.rStruct rest)).map some := by
            rw [List.map_drop, hEvalSplit, ← hmapSomeLen, List.drop_left]
          have hrec :=
            ih (cexp.drop (sizeOfShapeHOL (shapeOfHOLExact v))) hdrop hWfRest k value hget
          simpa only [List.map_cons, compFieldHOL, Nat.succ_ne_zero, if_false,
            Nat.succ_sub_one] using hrec

/-- Flapjack-specific staged constructor lemma for the `RField` leaf of the
    exact `compile_exp_val_rel` induction
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:187-214`). It is not a
    standalone HOL declaration: it consumes the induction hypothesis `hsub` for
    the sub-expression (the relation at the sub-expression only) and otherwise
    proves the leaf directly; the full `compile_exp_val_rel` theorem remains
    open (bead flapjack-4ac.5.81). -/
theorem compileExpValRelHOL_rfield {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (index : Nat) (subExpression : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hsub : ∀ (subValue : ValueHOL width) (subExpressions : List (CrepExpHOL width))
        (subShape : ShapeHOL),
        state.evalHOLFinite subExpression = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL subExpression = true →
        compileExpExactHOLW context subExpression = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.rfield index subExpression) = some value)
    (hlocalised : localisedExpHOL (.rfield index subExpression) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.rfield index subExpression) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hlocSub : localisedExpHOL subExpression = true := hlocalised
  rw [PanSemStateFiniteExact.evalHOLFinite_rfield] at heval
  cases hsubEval : state.evalHOLFinite subExpression with
  | none =>
      simp only [hsubEval] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some subValue =>
      cases subValue with
      | val word =>
          simp only [hsubEval] at heval
          exact absurd heval.symm (Option.some_ne_none value)
      | nStruct name fields =>
          simp only [hsubEval] at heval
          exact absurd heval.symm (Option.some_ne_none value)
      | rStruct values =>
          simp only [hsubEval] at heval
          cases hsubCompile : compileExpExactHOLW context subExpression with
          | mk subExpressions subShape =>
              have hsubRes := hsub (.rStruct values) subExpressions subShape hsubEval
                hstate hcode hlocals hlocSub hsubCompile
              obtain ⟨hsubMap, _hsubLen, hsubShape, hsubWf⟩ := hsubRes
              simp only [shapeOfHOLExact] at hsubShape
              simp only [compileExpExactHOLW, hsubCompile] at hcompile
              cases subShape with
              | one => exact absurd hsubShape (by simp)
              | named nm => exact absurd hsubShape (by simp)
              | comb shapes =>
                  injection hsubShape with hshapes
                  dsimp only at hcompile
                  cases hcf : compFieldHOL index shapes subExpressions with
                  | mk cfExprs cfShape =>
                      rw [hcf] at hcompile
                      injection hcompile with hE hS
                      have hWfShapes : isWfShapesExactHOL ([] : StructContextExact)
                          (values.map shapeOfHOLExact) = true := by
                        have h := hsubWf
                        rw [← hshapes, isWfShapeExactHOL_comb] at h
                        exact h
                      have hslice := compFieldHOL_slice targetState values subExpressions
                        hsubMap hWfShapes index value heval
                      simp only [hshapes, hcf, hE, hS] at hslice
                      refine ⟨hslice.1, ?_, ?_, ?_⟩
                      · simpa only [hslice.2.1.symm] using hslice.2.2.1
                      · exact hslice.2.1.symm
                      · simpa only [hslice.2.1.symm] using hslice.2.2.2

/-- Exact-carrier `Load32` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml`). This is a
    Flapjack-specific staged constructor lemma: it consumes the induction
    hypothesis `hsub` for the sub-expression and proves the leaf directly; the
    full `compile_exp_val_rel` theorem remains open (bead flapjack-4ac.5.81). -/
theorem compileExpValRelHOL_load32 {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (subExpression : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hsub : ∀ (subValue : ValueHOL width) (subExpressions : List (CrepExpHOL width))
        (subShape : ShapeHOL),
        state.evalHOLFinite subExpression = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL subExpression = true →
        compileExpExactHOLW context subExpression = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.load32 subExpression) = some value)
    (hlocalised : localisedExpHOL (.load32 subExpression) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.load32 subExpression) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hlocSub : localisedExpHOL subExpression = true := hlocalised
  rw [PanSemStateFiniteExact.evalHOLFinite_load32] at heval
  cases hsubEval : state.evalHOLFinite subExpression with
  | none =>
      simp only [hsubEval] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some subValue =>
      cases subValue with
      | val wlab =>
          cases wlab with
          | word word =>
              cases hload : panMemLoad32HOL state.memory state.memaddrs state.be word with
              | none =>
                  simp only [hsubEval, hload, Option.map_none] at heval
                  exact absurd heval.symm (Option.some_ne_none value)
              | some loaded =>
                  simp only [hsubEval, hload, Option.map_some, Option.some.injEq] at heval
                  cases hsubCompile : compileExpExactHOLW context subExpression with
                  | mk subExpressions subShape =>
                      have hsubRes := hsub (.val (.word word)) subExpressions subShape
                        hsubEval hstate hcode hlocals hlocSub hsubCompile
                      obtain ⟨hsubMap, hsubLen, hsubShape, _hsubWf⟩ := hsubRes
                      simp only [shapeOfHOLExact] at hsubShape
                      have hsubShapeOne : subShape = .one := hsubShape.symm
                      rw [hsubShapeOne] at hsubLen
                      simp only [flattenHOL, List.map_cons, List.map_nil] at hsubMap
                      simp only [sizeOfShapeHOL] at hsubLen
                      cases subExpressions with
                      | nil =>
                          simp only [List.map_nil] at hsubMap
                          exact absurd hsubMap (by simp)
                      | cons code rest =>
                          simp only [List.map_cons] at hsubMap
                          injection hsubMap with hcodeEq hrestMap
                          have hlenCons : rest.length = 0 := by
                            simp only [List.length_cons] at hsubLen
                            omega
                          have hrestNil : rest = [] := by
                            cases rest with
                            | nil => rfl
                            | cons x xs => simp at hlenCons
                          subst hrestNil
                          have hloadCrep : evalCrepSemHOLExp targetState (.load32 code) =
                              some (.word (BitVec.ofNat width loaded.toNat)) := by
                            have hmem : targetState.memory = state.memory := hstate.1.symm
                            have hmemaddrs : targetState.memaddrs = state.memaddrs :=
                              hstate.2.1.symm
                            have hbe : targetState.be = state.be :=
                              hstate.2.2.2.2.2.2.1.symm
                            simp only [evalCrepSemHOLExp, hcodeEq, hmem, hmemaddrs, hbe]
                            show Option.map
                                (fun loadedValue => HolWordLab.word
                                  (BitVec.ofNat width loadedValue.toNat))
                                (panMemLoad32HOL state.memory state.memaddrs state.be word) =
                              some (.word (BitVec.ofNat width loaded.toNat))
                            rw [hload]
                            rfl
                          have hcompile' := hcompile
                          simp only [compileExpExactHOLW] at hcompile'
                          rw [hsubCompile] at hcompile'
                          rw [hsubShapeOne] at hcompile'
                          injection hcompile' with hexpr hshape
                          rw [← heval, ← hexpr, ← hshape]
                          refine ⟨?_, ?_, ?_, ?_⟩
                          · simp only [List.map_cons, List.map_nil, hloadCrep, flattenHOL]
                          · simp only [List.length_cons, List.length_nil, sizeOfShapeHOL]
                          · simp only [shapeOfHOLExact]
                          · simp only [isWfShapeExactHOL]
      | nStruct structName fields =>
          simp only [hsubEval] at heval
          exact absurd heval.symm (Option.some_ne_none value)
      | rStruct subValues =>
          simp only [hsubEval] at heval
          exact absurd heval.symm (Option.some_ne_none value)

/-- Exact-carrier `LoadByte` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml`). This is a
    Flapjack-specific staged constructor lemma: it consumes the induction
    hypothesis `hsub` for the sub-expression and proves the leaf directly; the
    full `compile_exp_val_rel` theorem remains open (bead flapjack-4ac.5.81). -/
theorem compileExpValRelHOL_loadByte {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (subExpression : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hsub : ∀ (subValue : ValueHOL width) (subExpressions : List (CrepExpHOL width))
        (subShape : ShapeHOL),
        state.evalHOLFinite subExpression = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL subExpression = true →
        compileExpExactHOLW context subExpression = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.loadByte subExpression) = some value)
    (hlocalised : localisedExpHOL (.loadByte subExpression) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.loadByte subExpression) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hlocSub : localisedExpHOL subExpression = true := hlocalised
  rw [PanSemStateFiniteExact.evalHOLFinite_loadByte] at heval
  cases hsubEval : state.evalHOLFinite subExpression with
  | none =>
      simp only [hsubEval] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some subValue =>
      cases subValue with
      | val wlab =>
          cases wlab with
          | word word =>
              cases hload : panMemLoadByteHOL state.memory state.memaddrs state.be word with
              | none =>
                  simp only [hsubEval, hload, Option.map_none] at heval
                  exact absurd heval.symm (Option.some_ne_none value)
              | some loaded =>
                  simp only [hsubEval, hload, Option.map_some, Option.some.injEq] at heval
                  cases hsubCompile : compileExpExactHOLW context subExpression with
                  | mk subExpressions subShape =>
                      have hsubRes := hsub (.val (.word word)) subExpressions subShape
                        hsubEval hstate hcode hlocals hlocSub hsubCompile
                      obtain ⟨hsubMap, hsubLen, hsubShape, _hsubWf⟩ := hsubRes
                      simp only [shapeOfHOLExact] at hsubShape
                      have hsubShapeOne : subShape = .one := hsubShape.symm
                      rw [hsubShapeOne] at hsubLen
                      simp only [flattenHOL, List.map_cons, List.map_nil] at hsubMap
                      simp only [sizeOfShapeHOL] at hsubLen
                      cases subExpressions with
                      | nil =>
                          simp only [List.map_nil] at hsubMap
                          exact absurd hsubMap (by simp)
                      | cons code rest =>
                          simp only [List.map_cons] at hsubMap
                          injection hsubMap with hcodeEq hrestMap
                          have hlenCons : rest.length = 0 := by
                            simp only [List.length_cons] at hsubLen
                            omega
                          have hrestNil : rest = [] := by
                            cases rest with
                            | nil => rfl
                            | cons x xs => simp at hlenCons
                          subst hrestNil
                          have hloadCrep : evalCrepSemHOLExp targetState (.loadByte code) =
                              some (.word (BitVec.ofNat width loaded.toNat)) := by
                            have hmem : targetState.memory = state.memory := hstate.1.symm
                            have hmemaddrs : targetState.memaddrs = state.memaddrs :=
                              hstate.2.1.symm
                            have hbe : targetState.be = state.be :=
                              hstate.2.2.2.2.2.2.1.symm
                            simp only [evalCrepSemHOLExp, hcodeEq, hmem, hmemaddrs, hbe]
                            show Option.map
                                (fun loadedValue => HolWordLab.word
                                  (BitVec.ofNat width loadedValue.toNat))
                                (panMemLoadByteHOL state.memory state.memaddrs state.be word) =
                              some (.word (BitVec.ofNat width loaded.toNat))
                            rw [hload]
                            rfl
                          have hcompile' := hcompile
                          simp only [compileExpExactHOLW] at hcompile'
                          rw [hsubCompile] at hcompile'
                          rw [hsubShapeOne] at hcompile'
                          injection hcompile' with hexpr hshape
                          rw [← heval, ← hexpr, ← hshape]
                          refine ⟨?_, ?_, ?_, ?_⟩
                          · simp only [List.map_cons, List.map_nil, hloadCrep, flattenHOL]
                          · simp only [List.length_cons, List.length_nil, sizeOfShapeHOL]
                          · simp only [shapeOfHOLExact]
                          · simp only [isWfShapeExactHOL]
      | nStruct structName fields =>
          simp only [hsubEval] at heval
          exact absurd heval.symm (Option.some_ne_none value)
      | rStruct subValues =>
          simp only [hsubEval] at heval
          exact absurd heval.symm (Option.some_ne_none value)

/-- Exact-carrier `Cmp` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml`). This is a
    Flapjack-specific staged constructor lemma: it consumes the induction
    hypotheses `hleft`/`hright` for the two sub-expressions and proves the leaf
    directly; the full `compile_exp_val_rel` theorem remains open (bead
    flapjack-4ac.5.81). -/
theorem compileExpValRelHOL_cmp {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (operator : Cmp) (left right : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hleft : ∀ (subValue : ValueHOL width) (subExpressions : List (CrepExpHOL width))
        (subShape : ShapeHOL),
        state.evalHOLFinite left = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL left = true →
        compileExpExactHOLW context left = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (hright : ∀ (subValue : ValueHOL width) (subExpressions : List (CrepExpHOL width))
        (subShape : ShapeHOL),
        state.evalHOLFinite right = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL right = true →
        compileExpExactHOLW context right = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.cmp operator left right) = some value)
    (hlocalised : localisedExpHOL (.cmp operator left right) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.cmp operator left right) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hlocBoth : localisedExpHOL left = true ∧ localisedExpHOL right = true := by
    simpa only [localisedExpHOL, everyExpHOL, Bool.true_and, Bool.and_eq_true]
      using hlocalised
  obtain ⟨hlocLeft, hlocRight⟩ := hlocBoth
  rw [PanSemStateFiniteExact.evalHOLFinite_cmp] at heval
  cases hleftEval : state.evalHOLFinite left with
  | none =>
      simp only [hleftEval] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some leftValue =>
      cases leftValue with
      | val leftWordLab =>
          cases leftWordLab with
          | word lword =>
              cases hrightEval : state.evalHOLFinite right with
              | none =>
                  simp only [hleftEval, hrightEval] at heval
                  exact absurd heval.symm (Option.some_ne_none value)
              | some rightValue =>
                  cases rightValue with
                  | val rightWordLab =>
                      cases rightWordLab with
                      | word rword =>
                          simp only [hleftEval, hrightEval, Option.some.injEq] at heval
                          cases hleftCompile : compileExpExactHOLW context left with
                          | mk leftExps leftShape =>
                              cases hrightCompile : compileExpExactHOLW context right with
                              | mk rightExps rightShape =>
                                  have hleftRes := hleft (.val (.word lword)) leftExps leftShape
                                    hleftEval hstate hcode hlocals hlocLeft hleftCompile
                                  obtain ⟨hleftMap, hleftLen, hleftShape, _⟩ := hleftRes
                                  have hrightRes := hright (.val (.word rword)) rightExps rightShape
                                    hrightEval hstate hcode hlocals hlocRight hrightCompile
                                  obtain ⟨hrightMap, hrightLen, hrightShape, _⟩ := hrightRes
                                  simp only [shapeOfHOLExact] at hleftShape hrightShape
                                  have hleftShapeOne : leftShape = .one := hleftShape.symm
                                  have hrightShapeOne : rightShape = .one := hrightShape.symm
                                  rw [hleftShapeOne] at hleftLen
                                  rw [hrightShapeOne] at hrightLen
                                  simp only [flattenHOL, List.map_cons, List.map_nil] at hleftMap hrightMap
                                  simp only [sizeOfShapeHOL] at hleftLen hrightLen
                                  cases leftExps with
                                  | nil =>
                                      simp only [List.map_nil] at hleftMap
                                      exact absurd hleftMap (by simp)
                                  | cons lcode lrest =>
                                      simp only [List.map_cons] at hleftMap
                                      injection hleftMap with hlcodeEq _
                                      have hlrestNil : lrest = [] := by
                                        have hlenRest : lrest.length = 0 := by
                                          simp only [List.length_cons] at hleftLen
                                          omega
                                        cases lrest with
                                        | nil => rfl
                                        | cons _ _ => simp at hlenRest
                                      subst hlrestNil
                                      cases rightExps with
                                      | nil =>
                                          simp only [List.map_nil] at hrightMap
                                          exact absurd hrightMap (by simp)
                                      | cons rcode rrest =>
                                          simp only [List.map_cons] at hrightMap
                                          injection hrightMap with hrcodeEq _
                                          have hrrestNil : rrest = [] := by
                                            have hlenRest : rrest.length = 0 := by
                                              simp only [List.length_cons] at hrightLen
                                              omega
                                            cases rrest with
                                            | nil => rfl
                                            | cons _ _ => simp at hlenRest
                                          subst hrrestNil
                                          have hcmpCrep : evalCrepSemHOLExp targetState
                                              (.cmp operator lcode rcode) =
                                              some (.word (Compiler.Encoders.Asm.wordCmpResultHOL
                                                operator lword rword)) := by
                                            simp only [evalCrepSemHOLExp, hlcodeEq, hrcodeEq]
                                            rfl
                                          have hcompile' := hcompile
                                          simp only [compileExpExactHOLW] at hcompile'
                                          rw [hleftCompile] at hcompile'
                                          rw [hrightCompile] at hcompile'
                                          rw [hleftShapeOne] at hcompile'
                                          rw [hrightShapeOne] at hcompile'
                                          dsimp only at hcompile'
                                          injection hcompile' with hexpr hshape
                                          rw [← heval, ← hexpr, ← hshape]
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · simp only [List.map_cons, List.map_nil, hcmpCrep, flattenHOL,
                                              Compiler.Encoders.Asm.wordCmpResultHOL]
                                          · simp only [List.length_cons, List.length_nil, sizeOfShapeHOL]
                                          · simp only [shapeOfHOLExact]
                                          · simp only [isWfShapeExactHOL]
                  | nStruct structName fields =>
                      simp only [hleftEval, hrightEval] at heval
                      exact absurd heval.symm (Option.some_ne_none value)
                  | rStruct rightValues =>
                      simp only [hleftEval, hrightEval] at heval
                      exact absurd heval.symm (Option.some_ne_none value)
      | nStruct structName fields =>
          cases hrightEval : state.evalHOLFinite right <;>
            simp only [hleftEval, hrightEval] at heval <;>
            exact absurd heval.symm (Option.some_ne_none value)
      | rStruct leftValues =>
          cases hrightEval : state.evalHOLFinite right <;>
            simp only [hleftEval, hrightEval] at heval <;>
            exact absurd heval.symm (Option.some_ne_none value)

/-- Exact-carrier `Shift` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml`). This is a
    Flapjack-specific staged constructor lemma: it consumes the induction
    hypotheses `hleft`/`hright` for the two sub-expressions and proves the leaf
    directly; the full `compile_exp_val_rel` theorem remains open (bead
    flapjack-4ac.5.81). -/
theorem compileExpValRelHOL_shift {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (operator : Shift) (left right : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hleft : ∀ (subValue : ValueHOL width) (subExpressions : List (CrepExpHOL width))
        (subShape : ShapeHOL),
        state.evalHOLFinite left = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL left = true →
        compileExpExactHOLW context left = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (hright : ∀ (subValue : ValueHOL width) (subExpressions : List (CrepExpHOL width))
        (subShape : ShapeHOL),
        state.evalHOLFinite right = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL right = true →
        compileExpExactHOLW context right = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.shift operator left right) = some value)
    (hlocalised : localisedExpHOL (.shift operator left right) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.shift operator left right) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have hlocBoth : localisedExpHOL left = true ∧ localisedExpHOL right = true := by
    simpa only [localisedExpHOL, everyExpHOL, Bool.true_and, Bool.and_eq_true]
      using hlocalised
  obtain ⟨hlocLeft, hlocRight⟩ := hlocBoth
  rw [PanSemStateFiniteExact.evalHOLFinite_shift] at heval
  cases hleftEval : state.evalHOLFinite left with
  | none =>
      simp only [hleftEval] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some leftValue =>
      cases leftValue with
      | val leftWordLab =>
          cases leftWordLab with
          | word lword =>
              cases hrightEval : state.evalHOLFinite right with
              | none =>
                  simp only [hleftEval, hrightEval] at heval
                  exact absurd heval.symm (Option.some_ne_none value)
              | some rightValue =>
                  cases rightValue with
                  | val rightWordLab =>
                      cases rightWordLab with
                      | word rword =>
                          simp only [hleftEval, hrightEval] at heval
                          cases hshift : wordShiftHOL operator lword rword.toNat with
                          | none =>
                              simp only [hshift, Option.map_none] at heval
                              exact absurd heval.symm (Option.some_ne_none value)
                          | some sword =>
                              simp only [hshift, Option.map_some, Option.some.injEq] at heval
                              cases hleftCompile : compileExpExactHOLW context left with
                              | mk leftExps leftShape =>
                                  cases hrightCompile : compileExpExactHOLW context right with
                                  | mk rightExps rightShape =>
                                      have hleftRes := hleft (.val (.word lword)) leftExps leftShape
                                        hleftEval hstate hcode hlocals hlocLeft hleftCompile
                                      obtain ⟨hleftMap, hleftLen, hleftShape, _⟩ := hleftRes
                                      have hrightRes := hright (.val (.word rword)) rightExps rightShape
                                        hrightEval hstate hcode hlocals hlocRight hrightCompile
                                      obtain ⟨hrightMap, hrightLen, hrightShape, _⟩ := hrightRes
                                      simp only [shapeOfHOLExact] at hleftShape hrightShape
                                      have hleftShapeOne : leftShape = .one := hleftShape.symm
                                      have hrightShapeOne : rightShape = .one := hrightShape.symm
                                      rw [hleftShapeOne] at hleftLen
                                      rw [hrightShapeOne] at hrightLen
                                      simp only [flattenHOL, List.map_cons, List.map_nil] at hleftMap hrightMap
                                      simp only [sizeOfShapeHOL] at hleftLen hrightLen
                                      cases leftExps with
                                      | nil =>
                                          simp only [List.map_nil] at hleftMap
                                          exact absurd hleftMap (by simp)
                                      | cons lcode lrest =>
                                          simp only [List.map_cons] at hleftMap
                                          injection hleftMap with hlcodeEq _
                                          have hlrestNil : lrest = [] := by
                                            have hlenRest : lrest.length = 0 := by
                                              simp only [List.length_cons] at hleftLen
                                              omega
                                            cases lrest with
                                            | nil => rfl
                                            | cons _ _ => simp at hlenRest
                                          subst hlrestNil
                                          cases rightExps with
                                          | nil =>
                                              simp only [List.map_nil] at hrightMap
                                              exact absurd hrightMap (by simp)
                                          | cons rcode rrest =>
                                              simp only [List.map_cons] at hrightMap
                                              injection hrightMap with hrcodeEq _
                                              have hrrestNil : rrest = [] := by
                                                have hlenRest : rrest.length = 0 := by
                                                  simp only [List.length_cons] at hrightLen
                                                  omega
                                                cases rrest with
                                                | nil => rfl
                                                | cons _ _ => simp at hlenRest
                                              subst hrrestNil
                                              have hshiftCrep : evalCrepSemHOLExp targetState
                                                  (.shift operator lcode rcode) = some (.word sword) := by
                                                simp only [evalCrepSemHOLExp, hlcodeEq, hrcodeEq]
                                                show Option.map HolWordLab.word
                                                    (wordShiftHOL operator lword rword.toNat) =
                                                  some (.word sword)
                                                rw [hshift]
                                                rfl
                                              have hcompile' := hcompile
                                              simp only [compileExpExactHOLW] at hcompile'
                                              rw [hleftCompile] at hcompile'
                                              rw [hrightCompile] at hcompile'
                                              rw [hleftShapeOne] at hcompile'
                                              rw [hrightShapeOne] at hcompile'
                                              dsimp only at hcompile'
                                              injection hcompile' with hexpr hshape
                                              rw [← heval, ← hexpr, ← hshape]
                                              refine ⟨?_, ?_, ?_, ?_⟩
                                              · simp only [List.map_cons, List.map_nil, hshiftCrep, flattenHOL]
                                              · simp only [List.length_cons, List.length_nil, sizeOfShapeHOL]
                                              · simp only [shapeOfHOLExact]
                                              · simp only [isWfShapeExactHOL]
                  | nStruct structName fields =>
                      simp only [hleftEval, hrightEval] at heval
                      exact absurd heval.symm (Option.some_ne_none value)
                  | rStruct rightValues =>
                      simp only [hleftEval, hrightEval] at heval
                      exact absurd heval.symm (Option.some_ne_none value)
      | nStruct structName fields =>
          cases hrightEval : state.evalHOLFinite right <;>
            simp only [hleftEval, hrightEval] at heval <;>
            exact absurd heval.symm (Option.some_ne_none value)
      | rStruct leftValues =>
          cases hrightEval : state.evalHOLFinite right <;>
            simp only [hleftEval, hrightEval] at heval <;>
            exact absurd heval.symm (Option.some_ne_none value)

/-- Exact `Op` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:295-341`), over the exact
    finite-support carriers.  Flapjack-specific staged constructor lemma (HOL
    proves this case inside `compile_exp_val_rel`; there is no standalone exported
    declaration to tag). -/
theorem compileExpValRelHOL_op {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (operator : BinOp) (arguments : List (ExpHOL width))
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hrel : ∀ (expression : ExpHOL width), expression ∈ arguments →
        (value : ValueHOL width) → (expressions : List (CrepExpHOL width)) →
        (shape : ShapeHOL) →
        state.evalHOLFinite expression = some value →
        localisedExpHOL expression = true →
        compileExpExactHOLW context expression = (expressions, shape) →
        expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
        expressions.length = sizeOfShapeHOL shape ∧
        shapeOfHOLExact value = shape ∧
        isWfShapeExactHOL ([] : StructContextExact) shape = true)
    (heval : state.evalHOLFinite (.op operator arguments) = some value)
    (hlocalised : localisedExpHOL (.op operator arguments) = true)
    (hcompile : compileExpExactHOLW context (.op operator arguments) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  rw [PanSemStateFiniteExact.evalHOLFinite_op] at heval
  have hlocArgs : everyExpListHOL (width := width) localisedExpPredHOL arguments = true :=
    hlocalised
  cases hvals : state.evalListHOLFinite arguments with
  | none =>
      simp only [hvals] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some values =>
      by_cases hall : values.all valueIsWord = true
      · simp only [hvals, hall, if_true] at heval
        cases hop : wordOpHOL operator (values.map valueWord) with
        | none =>
            simp only [hop] at heval
            exact absurd heval.symm (Option.some_ne_none value)
        | some word =>
            simp only [hop, Option.map_some, Option.some.injEq] at heval
            obtain ⟨heads, hcheads, hheadsEval⟩ :=
              cexpHeads_compileExpListValRelHOL state context targetState arguments
                hrel values (compileExpExactHOLWList context arguments) hvals hlocArgs hall rfl
            simp only [compileExpExactHOLW] at hcompile
            rw [hcheads] at hcompile
            injection hcompile with hexpr hshape
            have hopEval : evalCrepSemHOLExp targetState (.op operator heads) =
                some (.word word) := by
              simp only [evalCrepSemHOLExp, hheadsEval]
              show Option.map HolWordLab.word
                  (wordOpHOL operator
                    ((List.map (fun v => HolWordLab.word (valueWord (width := width) v)) values).map
                      (fun value => match value with | HolWordLab.word word => word))) =
                some (.word word)
              have hExtract :
                  (List.map (fun v => HolWordLab.word (valueWord (width := width) v)) values).map
                      (fun value => match value with | HolWordLab.word word => word) =
                    values.map (valueWord (width := width)) := by
                rw [List.map_map]
                apply List.map_congr_left
                intro v _
                rfl
              rw [hExtract, hop]
              rfl
            rw [← heval, ← hexpr, ← hshape]
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [List.map_cons, List.map_nil, hopEval, flattenHOL]
            · simp only [List.length_cons, List.length_nil, sizeOfShapeHOL]
            · simp only [shapeOfHOLExact]
            · simp only [isWfShapeExactHOL]
      · have hfalse : values.all valueIsWord = false := by
          cases hb : values.all valueIsWord with
          | false => rfl
          | true => exact absurd hb hall
        simp only [hvals, hfalse, Bool.false_eq_true, if_false] at heval
        exact absurd heval.symm (Option.some_ne_none value)

private theorem crepOpCrepWord_compilePanOp {width : Nat} [NeZero width]
    (operator : PanOp) (arguments : List (BitVec width)) :
    crepOpCrepWord (compilePanOp operator) arguments = panOpHOL operator arguments := by
  cases operator with
  | mul =>
      cases arguments with
      | nil => rfl
      | cons left rest =>
          cases rest with
          | nil => rfl
          | cons right tail => cases tail <;> rfl

/-- Flapjack-specific staged constructor lemma for the `Panop` arm of HOL
    `compile_exp_val_rel` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml`,
    the `Panop` case). Mirrors `compileExpValRelHOL_op` with `panOpHOL` in place
    of `wordOpHOL` and the compiled `.crepOp (compilePanOp operator)`, related
    by `crepOpCrepWord_compilePanOp`. Not an exact HOL declaration (HOL proves
    this inside `compile_exp_val_rel`); no `@[hol]` tag. -/
theorem compileExpValRelHOL_panop {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (operator : PanOp) (arguments : List (ExpHOL width))
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hrel : ∀ (expression : ExpHOL width), expression ∈ arguments →
        (value : ValueHOL width) → (expressions : List (CrepExpHOL width)) →
        (shape : ShapeHOL) →
        state.evalHOLFinite expression = some value →
        localisedExpHOL expression = true →
        compileExpExactHOLW context expression = (expressions, shape) →
        expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
        expressions.length = sizeOfShapeHOL shape ∧
        shapeOfHOLExact value = shape ∧
        isWfShapeExactHOL ([] : StructContextExact) shape = true)
    (heval : state.evalHOLFinite (.panop operator arguments) = some value)
    (hlocalised : localisedExpHOL (.panop operator arguments) = true)
    (hcompile : compileExpExactHOLW context (.panop operator arguments) =
      (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  rw [PanSemStateFiniteExact.evalHOLFinite_panop] at heval
  have hlocArgs : everyExpListHOL (width := width) localisedExpPredHOL arguments = true :=
    hlocalised
  cases hvals : state.evalListHOLFinite arguments with
  | none =>
      simp only [hvals] at heval
      exact absurd heval.symm (Option.some_ne_none value)
  | some values =>
      by_cases hall : values.all valueIsWord = true
      · simp only [hvals, hall, if_true] at heval
        cases hop : panOpHOL operator (values.map valueWord) with
        | none =>
            simp only [hop] at heval
            exact absurd heval.symm (Option.some_ne_none value)
        | some word =>
            simp only [hop, Option.map_some, Option.some.injEq] at heval
            obtain ⟨heads, hcheads, hheadsEval⟩ :=
              cexpHeads_compileExpListValRelHOL state context targetState arguments
                hrel values (compileExpExactHOLWList context arguments) hvals hlocArgs hall rfl
            simp only [compileExpExactHOLW] at hcompile
            rw [hcheads] at hcompile
            injection hcompile with hexpr hshape
            have hopEval : evalCrepSemHOLExp targetState (.crepOp (compilePanOp operator) heads) =
                some (.word word) := by
              simp only [evalCrepSemHOLExp, hheadsEval]
              show Option.map HolWordLab.word
                  (crepOpCrepWord (compilePanOp operator)
                    ((List.map (fun v => HolWordLab.word (valueWord (width := width) v)) values).map
                      (fun value => match value with | HolWordLab.word word => word))) =
                some (.word word)
              have hExtract :
                  (List.map (fun v => HolWordLab.word (valueWord (width := width) v)) values).map
                      (fun value => match value with | HolWordLab.word word => word) =
                    values.map (valueWord (width := width)) := by
                rw [List.map_map]
                apply List.map_congr_left
                intro v _
                rfl
              rw [hExtract, crepOpCrepWord_compilePanOp, hop]
              rfl
            rw [← heval, ← hexpr, ← hshape]
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [List.map_cons, List.map_nil, hopEval, flattenHOL]
            · simp only [List.length_cons, List.length_nil, sizeOfShapeHOL]
            · simp only [shapeOfHOLExact]
            · simp only [isWfShapeExactHOL]
      · have hfalse : values.all valueIsWord = false := by
          cases hb : values.all valueIsWord with
          | false => rfl
          | true => exact absurd hb hall
        simp only [hvals, hfalse, Bool.false_eq_true, if_false] at heval
        exact absurd heval.symm (Option.some_ne_none value)

/-- The exact `crepSem$mem_load_def` body at one address (`crepSemScript.sml:48-51`);
this helper removes only the surrounding target-state record. -/
private def memLoadFlatTargetHOL {width : Nat} [NeZero width]
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → HolWordLab width) (address : BitVec width) :
    Option (HolWordLab width) :=
  if domain address then some (memory address) else none

/- Mutual strided-read analogue of HOL `mem_loads_flat_rel`
   (`crepPropsScript.sml:66-99`), using the shape clause of
   `mem_load_flat_rel` (`:102-109`). It follows the HOL list induction: the
   append split uses the length theorem below to establish the tail stride.
   This helper is intentionally untagged: it is over Lean's exact indexed
   carriers and exact evaluator, but is not itself the source theorem's shared
   Pan/Crep state statement. -/
private theorem memLoadHOLExact_flatRead_mutual {width : Nat} [NeZero width]
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → HolWordLab width) :
    ∀ (shape : ShapeHOL) (address : BitVec width) (context : StructContextHOLM),
      isWfShapeExactHOL ([] : StructContextExact) shape = true →
      ∀ value, memLoadHOLExact shape address domain memory context = some value →
      ∀ (n : Nat) (hn : n < (flattenHOL value).length),
        memLoadFlatTargetHOL domain memory
          (address + bytesInWordHOL width * BitVec.ofNat width n) =
            some ((flattenHOL value)[n]'hn) := by
  apply memLoadHOLExact.induct (domain := domain) (memory := memory)
    (motive1 := fun shape address context =>
      isWfShapeExactHOL ([] : StructContextExact) shape = true →
      ∀ value, memLoadHOLExact shape address domain memory context = some value →
      ∀ (n : Nat) (hn : n < (flattenHOL value).length),
        memLoadFlatTargetHOL domain memory
          (address + bytesInWordHOL width * BitVec.ofNat width n) =
            some ((flattenHOL value)[n]'hn))
    (motive2 := fun _ _ _ => True)
    (motive3 := fun shapes address context =>
      isWfShapesExactHOL ([] : StructContextExact) shapes = true →
      ∀ values, memLoadsHOLExact shapes address domain memory context = some values →
      ∀ (n : Nat) (hn : n < ((values.map flattenHOL).flatten).length),
        memLoadFlatTargetHOL domain memory
          (address + bytesInWordHOL width * BitVec.ofNat width n) =
            some (((values.map flattenHOL).flatten)[n]'hn))
  case case1 =>
    intro address context hdom _hwf value hload n hn
    simp only [memLoadHOLExact, if_pos hdom] at hload
    injection hload with hvalue
    subst value
    have hn0 : n = 0 := by simpa [flattenHOL] using hn
    subst n
    simp [memLoadFlatTargetHOL, flattenHOL, hdom]
  case case2 =>
    intro address context hndom _hwf value hload n hn
    simp only [memLoadHOLExact, if_neg hndom] at hload
    contradiction
  case case3 =>
    intro address context shapes values hloads ihShapes hwf value hload n hn
    rw [memLoadHOLExact.eq_2, hloads] at hload
    injection hload with hvalue
    subst value
    have hwfShapes : isWfShapesExactHOL ([] : StructContextExact) shapes = true := by
      simpa only [isWfShapeExactHOL_comb] using hwf
    have hread := ihShapes hwfShapes values hloads n (by simpa [flattenHOL] using hn)
    simpa [flattenHOL] using hread
  case case4 =>
    intro address context shapes hfail ihShapes _hwf value hload n hn
    rw [memLoadHOLExact.eq_2, hfail] at hload
    simp at hload
  case case5 =>
    intro address name hwf value hload n hn
    simp [isWfShapeExactHOL] at hwf
  case case6 =>
    intro address candidate info rest fields hfields _ihFields hwf value hload n hn
    simp [isWfShapeExactHOL] at hwf
  case case7 =>
    intro address candidate info rest _hfields _ihFields hwf value hload n hn
    simp [isWfShapeExactHOL] at hwf
  case case8 =>
    intro address name candidate info rest hne ihShape hwf value hload n hn
    simp [isWfShapeExactHOL] at hwf
  case case9 =>
    intro address context
    trivial
  case case10 =>
    intro address context field shape rest value values htail hhead ihHead ihTail
    trivial
  case case11 =>
    intro address context field shape rest hfail ihHead ihTail
    trivial
  case case12 =>
    intro address context hwf values hloads n hn
    simp only [memLoadsHOLExact] at hloads
    injection hloads with hvalues
    subst values
    simp at hn
  case case13 =>
    intro address context shape rest headValue tailValues htail hhead
      ihHead ihTail hwfList values hload n hn
    rw [memLoadsHOLExact.eq_2, hhead, htail] at hload
    injection hload with hvalues
    subst values
    have hwfParts :
        isWfShapeExactHOL ([] : StructContextExact) shape = true ∧
          isWfShapesExactHOL ([] : StructContextExact) rest = true := by
      simpa only [isWfShapesExactHOL_cons, Bool.and_eq_true] using hwfList
    have hheadLength := memLoadHOLExact_length_flatten_context
      domain memory shape address context hwfParts.1 headValue hhead
    let headFlat := flattenHOL headValue
    let tailFlat := (tailValues.map flattenHOL).flatten
    let tailAddress := address + bytesInWordHOL width *
      BitVec.ofNat width (sizeOfShapeWithContextHOL context shape)
    have happend : ((headValue :: tailValues).map flattenHOL).flatten =
        headFlat ++ tailFlat := by simp [headFlat, tailFlat]
    have hflatLen : ((headValue :: tailValues).map flattenHOL).flatten.length =
        headFlat.length + tailFlat.length := by
      simp [headFlat, tailFlat]
    have hnAppend : n < headFlat.length + tailFlat.length := by
      rw [← hflatLen]
      exact hn
    have hidx : n < (headFlat ++ tailFlat).length := by
      simpa [List.length_append] using hnAppend
    by_cases hnHead : n < headFlat.length
    · have hread := ihHead hwfParts.1 headValue hhead n hnHead
      have hget : (headFlat ++ tailFlat)[n]'hidx = headFlat[n]'hnHead := by
        exact List.getElem_append_left hnHead
      simpa [memLoadFlatTargetHOL, headFlat, tailFlat, flattenHOL, hget] using hread
    · have hlarge : headFlat.length ≤ n := Nat.le_of_not_lt hnHead
      let nTail := n - headFlat.length
      have hnTail : nTail < tailFlat.length := by omega
      have hsplit : n = headFlat.length + nTail := by omega
      have hsize : sizeOfShapeWithContextHOL context shape = headFlat.length :=
        hheadLength.symm
      have haddress :
          address + bytesInWordHOL width * BitVec.ofNat width n =
            tailAddress + bytesInWordHOL width * BitVec.ofNat width nTail := by
        simp only [tailAddress, hsize, hsplit, BitVec.ofNat_add,
          BitVec.mul_add, BitVec.add_assoc]
      have hread := ihTail hwfParts.2 tailValues htail nTail hnTail
      have hget : (headFlat ++ tailFlat)[n]'hidx = tailFlat[nTail]'hnTail := by
        rw [List.getElem_append_right hlarge]
      simpa [memLoadFlatTargetHOL, headFlat, tailFlat, flattenHOL,
        haddress, hget] using hread
  case case14 =>
    intro address context shape rest hfail _ihHead _ihTail _hwfList values hload n hn
    rw [memLoadsHOLExact.eq_2] at hload
    cases hhead : memLoadHOLExact shape address domain memory context with
    | none => simp [hhead] at hload
    | some headValue =>
      let tailAddress := address + bytesInWordHOL width *
        BitVec.ofNat width (sizeOfShapeWithContextHOL context shape)
      cases htail : memLoadsHOLExact rest tailAddress domain memory context with
      | none =>
        have htail' := htail
        dsimp [tailAddress] at htail'
        simp [hhead, htail'] at hload
      | some tailValues => exact (hfail headValue tailValues hhead htail).elim

/- Exact-carrier analogue of HOL `mem_load_flat_rel`
   (`cakeml/pancake/semantics/crepPropsScript.sml:102-109`). Given the exact
   equalities between the Pan memory/domain arguments and the Crep state's
   memory/domain, a successful `memLoadHOLExact` result, and nil-context
   well-formedness, the Crep `mem_load_def` body returns element `n` at the
   source theorem's `LENGTH (TAKE n ...)` address. This declaration stays
   untagged: the HOL word is represented here by `BitVec width`, and the target
   state type is owned by the separate CrepSem module; the current tag checker
   requires an owning finite-map carrier and witness in the same module before
   that state representation can be qualified. -/
theorem memLoadFlatRelHOLExact {width : Nat} {σ : Type} [NeZero width]
    (domain : BitVec width → Prop) [hd : DecidablePred domain]
    (memory : BitVec width → HolWordLab width)
    (target : CrepSemHOLState width σ)
    [ht : DecidablePred target.memaddrs]
    (hmemaddrs : domain = target.memaddrs)
    (hmemory : memory = target.memory)
    (shape : ShapeHOL) (address : BitVec width) (context : StructContextHOLM)
    (value : ValueHOL width) (n : Nat)
    (hload : memLoadHOLExact shape address domain memory context = some value)
    (hn : n < (flattenHOL value).length)
    (hwf : isWfShapeExactHOL ([] : StructContextExact) shape = true) :
    memLoadCrepSemHOL
        (address + bytesInWordHOL width * BitVec.ofNat width
          ((flattenHOL value).take n).length) target =
      some ((flattenHOL value)[n]'hn) := by
  have hread := memLoadHOLExact_flatRead_mutual
    domain memory shape address context hwf value hload n hn
  have htake : ((flattenHOL value).take n).length = n :=
    List.length_take_of_le (Nat.le_of_lt hn)
  rw [htake]
  simpa [memLoadCrepSemHOL, ← hmemaddrs, ← hmemory, memLoadFlatTargetHOL] using hread

end Flapjack
