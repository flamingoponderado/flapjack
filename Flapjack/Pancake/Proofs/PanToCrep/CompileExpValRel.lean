import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Semantics.PanSem.EvalFinite
import Flapjack.Pancake.Semantics.PanProps.LocalisedExpSimps
import Flapjack.Pancake.Semantics.CrepProps.MemLoadFlatRel

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

The full theorem is assembled at the end of this module as `compileExpValRelHOL`
(bead `flapjack-4ac.5.81`), the exact target of HOL `compile_exp_val_rel`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130`). It carries the
combined `(fmap_as_finite_support_relation := [...])` +
`(words_as_type_indexed_bitvec)` qualifier (bead `flapjack-4ac.5.81.14`): the
HOL theorem is polymorphic in the word dimension (`'a word`) and the FFI-state
type (the `('a,'b) state` parameter), while this rendering fixes the positive
width `BitVec width` (`[NeZero width]`) and the universe-0 host `σ : Type`, and
represents the HOL state/context maps by the finite-support carriers
`PanSemStateFiniteExact` / `CrepSemHOLState` / `PanToCrepContextExact`. The
relation list records exactly the carrier fields the three relation hypotheses
traverse; the same-module per-carrier witnesses below validate those carriers.
The individual `compileExpValRelHOL_<constructor>` case lemmas are Flapjack
proof infrastructure and are untagged.
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

    This is the exact-carrier statement assembled by `compileExpValRelHOL` below
    (bead `flapjack-4ac.5.81`). -/
def compileExpValRelHOLProp {width : Nat} {σ : Type} [NeZero width]
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

/-- Exact-carrier general `Load` case of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:217-256`). This staged
    case consumes the induction hypothesis for the address expression, then
    composes the exact `mem_load_flat_rel` and `eval_load_shape_el_rel`
    counterparts. It keeps HOL's successful source-evaluation premise and
    proves all four conclusions without assuming target evaluation. HOL proves
    this as a case of `compile_exp_val_rel`, not as a separately exported
    theorem, so this case lemma is intentionally untagged. -/
theorem compileExpValRelHOL_load {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [_ht : DecidablePred targetState.memaddrs]
    (shape : ShapeHOL) (address : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (outputShape : ShapeHOL)
    (hsub : ∀ (subValue : ValueHOL width) (subExpressions : List (CrepExpHOL width))
        (subShape : ShapeHOL),
        state.evalHOLFinite address = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL address = true →
        compileExpExactHOLW context address = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.load shape address) = some value)
    (hlocalised : localisedExpHOL (.load shape address) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.load shape address) =
      (expressions, outputShape)) :
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL outputShape ∧
    shapeOfHOLExact value = outputShape ∧
    isWfShapeExactHOL ([] : StructContextExact) outputShape = true := by
  rw [PanSemStateFiniteExact.evalHOLFinite_load] at heval
  by_cases hwfSource : isWfShapeExactHOL state.structs shape = true
  · simp only [if_pos hwfSource] at heval
    cases haddress : state.evalHOLFinite address with
    | none =>
        simp only [haddress] at heval
        exact absurd heval.symm (Option.some_ne_none value)
    | some addressValue =>
        cases addressValue with
        | val addressLab =>
            cases addressLab with
            | word addressWord =>
                simp only [haddress] at heval
                cases hmemLoad : memLoadHOLExact shape addressWord state.memaddrs
                    state.memory state.structs with
                | none =>
                    simp only [hmemLoad] at heval
                    exact absurd heval.symm (Option.some_ne_none value)
                | some loaded =>
                    simp only [hmemLoad, Option.some.injEq] at heval
                    have hvalue : value = loaded := heval.symm
                    have hstructs := panToCrepStateRelFiniteExact_structs state targetState hstate
                    have hwf : isWfShapeExactHOL ([] : StructContextExact) shape = true := by
                      simpa only [hstructs] using hwfSource
                    have hloadedShape : shapeOfHOLExact loaded = shape :=
                      memLoadHOLExact_some_shapeOf_eq shape addressWord state.memaddrs
                        state.memory state.structs loaded hmemLoad
                    have hmemLoadTarget :
                        memLoadHOLExact shape addressWord targetState.memaddrs
                          targetState.memory state.structs = some loaded := by
                      simpa only [hstate.2.1, hstate.1] using hmemLoad
                    have hloadedLength : (flattenHOL loaded).length = sizeOfShapeHOL shape := by
                      have hwfLoaded : isWfShapeExactHOL ([] : StructContextExact)
                          (shapeOfHOLExact loaded) = true := by
                        simpa only [hloadedShape] using hwf
                      simpa only [hloadedShape] using
                        flattenHOL_length_eq_sizeOfShapeHOL loaded hwfLoaded
                    cases hsubCompile : compileExpExactHOLW context address with
                    | mk subExpressions subShape =>
                        have hsubEval : state.evalHOLFinite address =
                            some (.val (.word addressWord)) := haddress
                        have hlocalisedAddress : localisedExpHOL address = true := by
                          simpa only [localisedExpSimpsHOL.2.2.2.2.2.2.1] using hlocalised
                        have hsubResult := hsub (.val (.word addressWord))
                          subExpressions subShape hsubEval hstate hcode hlocals
                          hlocalisedAddress hsubCompile
                        obtain ⟨hsubMap, hsubLen, hsubShape, _hsubWf⟩ := hsubResult
                        have hsubShapeOne : subShape = .one := by
                          simpa only [shapeOfHOLExact] using hsubShape.symm
                        rw [hsubShapeOne, sizeOfShapeHOL] at hsubLen
                        have hsubOne : subExpressions.length = 1 := hsubLen
                        cases subExpressions with
                        | nil => simp at hsubOne
                        | cons addressCode addressRest =>
                            have hrestEmpty : addressRest = [] := by
                              cases addressRest with
                              | nil => rfl
                              | cons x xs => simp at hsubOne
                            subst addressRest
                            simp only [List.map_cons, List.map_nil] at hsubMap
                            have htargetAddress :
                                evalCrepSemHOLExp targetState addressCode =
                                  some (.word addressWord) := by
                              simpa [flattenHOL] using hsubMap
                            have hcompileLoad := hcompile
                            simp only [compileExpExactHOLW] at hcompileLoad
                            rw [hsubCompile] at hcompileLoad
                            injection hcompileLoad with hExpressions hOutputShape
                            subst outputShape
                            subst expressions
                            have hmap :
                                (loadShapeBytesHOLW (0 : BitVec width)
                                    (sizeOfShapeHOL shape) addressCode).map
                                    (evalCrepSemHOLExp targetState) =
                                  (flattenHOL loaded).map some := by
                              apply List.ext_getElem
                              · simp only [List.length_map, length_loadShapeHOLW,
                                  hloadedLength]
                              · intro index hleft hright
                                have hindex : index < sizeOfShapeHOL shape := by
                                  simpa only [List.length_map, length_loadShapeHOLW] using hleft
                                have hflatIndex : index < (flattenHOL loaded).length := by
                                  simpa only [List.length_map] using hright
                                have hgenerated := eval_loadShapeBytesHOLW_getElem
                                  targetState (0 : BitVec width) (sizeOfShapeHOL shape)
                                  addressCode index hindex
                                have hflat := memLoadFlatRelHOLExact targetState shape
                                  addressWord state.structs loaded index hmemLoadTarget
                                  hflatIndex hwf
                                have htake : ((flattenHOL loaded).take index).length = index :=
                                  List.length_take_of_le (Nat.le_of_lt hflatIndex)
                                rw [htake] at hflat
                                rw [List.getElem_map (evalCrepSemHOLExp targetState),
                                  List.getElem_map some]
                                change evalCrepSemHOLExp targetState
                                    ((loadShapeBytesHOLW (0 : BitVec width)
                                      (sizeOfShapeHOL shape) addressCode)[index]'(by
                                      simpa [length_loadShapeHOLW] using hleft)) =
                                  some ((flattenHOL loaded)[index]'hflatIndex)
                                calc
                                  evalCrepSemHOLExp targetState
                                      ((loadShapeBytesHOLW (0 : BitVec width)
                                        (sizeOfShapeHOL shape) addressCode)[index]'(by
                                        simpa only [length_loadShapeHOLW] using hindex)) =
                                        evalCrepSemHOLExp targetState
                                        (.load (.op .add [addressCode,
                                          .const (BitVec.ofNat width (width / 8) *
                                            BitVec.ofNat width index)])) := by
                                        have hgenerated' := hgenerated
                                        have hzero : (0 : BitVec width) +
                                            (BitVec.ofNat width (width / 8) *
                                              BitVec.ofNat width index) =
                                            BitVec.ofNat width (width / 8) *
                                              BitVec.ofNat width index := BitVec.zero_add _
                                        rw [hzero] at hgenerated'
                                        exact hgenerated'
                                  _ = memLoadCrepSemHOL
                                      (addressWord + bytesInWordHOL width *
                                        BitVec.ofNat width index) targetState := by
                                        simp [evalCrepSemHOLExp, htargetAddress,
                                          wordOpHOL, wordOp, bytesInWordHOL,
                                          memLoadCrepSemHOL] <;> rfl
                                  _ = some ((flattenHOL loaded)[index]'(by
                                        simpa only [hloadedLength] using hindex)) := hflat
                            have hshape : shapeOfHOLExact loaded = shape := hloadedShape
                            have hloadedWf : isWfShapeExactHOL
                                ([] : StructContextExact) shape = true := hwf
                            refine ⟨?_, ?_, ?_, ?_⟩
                            · simpa only [hvalue] using hmap
                            · simp only [length_loadShapeHOLW]
                            · simpa only [hvalue, shapeOfHOLExact] using hshape
                            · exact hloadedWf
        | nStruct _ _ =>
            simp only [haddress] at heval
            exact absurd heval.symm (Option.some_ne_none value)
        | rStruct _ =>
            simp only [haddress] at heval
            exact absurd heval.symm (Option.some_ne_none value)
  · simp [hwfSource] at heval

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

/- Same-module canonical relation witnesses for the combined qualifier on
   `compileExpValRelHOL`. Declared in a fresh namespace so they do not clash
   with the identically named witnesses in the imported state-relation modules;
   the reference checker matches the unqualified name within this module. -/
namespace CompileExpValRelRelationWitnesses

/-- Same-module canonical relation witness for the imported `PanSemStateFiniteExact`
    carrier, whose `globals`, `code`, and `locals` fields are traversed by the
    `compile_exp_val_rel` hypotheses (`state_rel`, `code_rel`, `locals_rel`). It
    forwards the canonical `toExact`/`ofExact` roundtrip of the finite-support
    carrier with its broad `PanSemStateExact` counterpart. Flapjack
    representation infrastructure only. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module canonical relation witness for the imported `CrepSemHOLState`
    carrier, whose `code` and `locals` fields are traversed by
    `compile_exp_val_rel`'s `code_rel`/`locals_rel` hypotheses. It forwards the
    canonical `toBroad`/`ofBroad` roundtrip with the broad `CrepSemBroadState`
    counterpart. Flapjack representation infrastructure only. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

/-- Same-module canonical relation witness for the imported
    `PanToCrepContextExact` carrier, whose `vars`, `funcs`, and `eids` fields are
    traversed by `compile_exp_val_rel`'s `code_rel`/`locals_rel` hypotheses. It
    forwards the canonical `toBroad`/`ofBroad` roundtrip with the broad
    `PanToCrepContextBroad` counterpart. Flapjack representation infrastructure
    only. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness context

end CompileExpValRelRelationWitnesses

/-- Assembled exact-carrier counterpart of HOL `compile_exp_val_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130`): the full
    expression-evaluation / compilation correspondence over the exact
    `PanSemStateFiniteExact` / `CrepSemHOLState` carriers.  Built by structural
    recursion on the expression, dispatching every constructor to its
    source-reviewed case lemma.

    Clause-for-clause comparison with the HOL statement: the six premises
    (`panSem$eval s e = SOME v`, `state_rel s t`, `code_rel ct s.code t.code`,
    `locals_rel ct s.locals t.locals`, `localised_exp e`, `compile_exp ct e =
    (es, sh)`) render as `state.evalHOLFinite expression = some value`,
    `panToCrepStateRelFiniteExact state targetState`,
    `codeRelExactHOLW context state.code targetState.code`,
    `panToCrepLocalsRelFiniteExact context state.locals targetState.locals`,
    `localisedExpHOL expression = true`, and `compileExpExactHOLW context
    expression = (expressions, shape)`; the four conclusions render as
    `expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map
    some`, `expressions.length = sizeOfShapeHOL shape`, `shapeOfHOLExact value =
    shape`, and `isWfShapeExactHOL ([] : StructContextExact) shape = true`. No
    hypothesis, side condition, quantifier, or conclusion differs.

    The combined `(fmap_as_finite_support_relation := [...])` +
    `(words_as_type_indexed_bitvec)` qualifier records the only representation
    differences: HOL is polymorphic in the word dimension (`'a word`) and the
    FFI-state type, whereas this statement fixes the positive width
    `BitVec width` (`[NeZero width]`) and the universe-0 host `σ : Type`; and the
    HOL state/context maps are represented by the finite-support carriers. The
    relation entries are exactly the fields the premises traverse: `state_rel`
    reads `PanSemStateFiniteExact.globals`; `code_rel` reads
    `PanSemStateFiniteExact.code` / `CrepSemHOLState.code` and
    `PanToCrepContextExact.funcs`/`eids`; `locals_rel` reads
    `PanToCrepContextExact.vars` and the `locals` fields of both states. The
    same-module witnesses above validate the three carriers. No cross-assistant
    agreement theorem is required for this tag. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_exp_val_rel"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals,
    PanSemStateFiniteExact.code, PanSemStateFiniteExact.locals,
    CrepSemHOLState.code, CrepSemHOLState.locals,
    PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem compileExpValRelHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [ht : DecidablePred targetState.memaddrs] :
    compileExpValRelHOLProp state context targetState := by
  let Conclusion : ValueHOL width → List (CrepExpHOL width) → ShapeHOL → Prop :=
    fun value expressions shape =>
      expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
      expressions.length = sizeOfShapeHOL shape ∧
      shapeOfHOLExact value = shape ∧
      isWfShapeExactHOL ([] : StructContextExact) shape = true
  let Case : ExpHOL width → Prop := fun e =>
    ∀ (value : ValueHOL width) (expressions : List (CrepExpHOL width)) (shape : ShapeHOL),
      state.evalHOLFinite e = some value →
      panToCrepStateRelFiniteExact state targetState →
      codeRelExactHOLW context state.code targetState.code →
      panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
      localisedExpHOL e = true →
      compileExpExactHOLW context e = (expressions, shape) →
      Conclusion value expressions shape
  exact ExpHOL.rec
    (motive_1 := Case)
    (motive_2 := fun l => ∀ e ∈ l, Case e)
    (motive_3 := fun l => ∀ p ∈ l, Case p.2)
    (motive_4 := fun p => Case p.2)
    (fun word => by
      intro value expressions shape heval _hstate _hcode _hlocals _hlocalised hcompile
      exact compileExpValRelHOL_const state context targetState word value expressions shape
        heval hcompile)
    (fun kind name => by
      intro value expressions shape heval _hstate _hcode hlocals hlocalised hcompile
      cases kind
      · exact compileExpValRelHOL_var_local state context targetState name value
          expressions shape heval hlocals hcompile
      · exact compileExpValRelHOL_var_global state context targetState name value
          expressions shape heval hlocalised hcompile)
    (fun fields ih => by
      intro value expressions shape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_rstruct state context targetState fields value expressions shape
        (fun e he v es sh hev hl hc => ih e he v es sh hev hstate hcode hlocals hl hc)
        heval hlocalised hcompile)
    (fun index subExpression ih => by
      intro value expressions shape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_rfield state context targetState index subExpression value
        expressions shape
        (fun sv ses ssh hev hs hc hl hcomp => ih sv ses ssh hev hs hc hl hcomp)
        heval hlocalised hstate hcode hlocals hcompile)
    (fun name fields _ih => by
      intro value expressions shape heval hstate _hcode _hlocals _hlocalised hcompile
      exact compileExpValRelHOL_nstruct state context targetState name fields value
        expressions shape heval hstate hcompile)
    (fun name value' _ih => by
      intro value expressions shape heval hstate _hcode _hlocals _hlocalised hcompile
      exact compileExpValRelHOL_nfield state context targetState name value' value
        expressions shape heval hstate hcompile)
    (fun shape address ih => by
      intro value expressions outputShape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_load state context targetState shape address value expressions
        outputShape
        (fun sv ses ssh hev hs hc hl hcomp => ih sv ses ssh hev hs hc hl hcomp)
        heval hlocalised hstate hcode hlocals hcompile)
    (fun subExpression ih => by
      intro value expressions shape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_load32 state context targetState subExpression value
        expressions shape
        (fun sv ses ssh hev hs hc hl hcomp => ih sv ses ssh hev hs hc hl hcomp)
        heval hlocalised hstate hcode hlocals hcompile)
    (fun subExpression ih => by
      intro value expressions shape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_loadByte state context targetState subExpression value
        expressions shape
        (fun sv ses ssh hev hs hc hl hcomp => ih sv ses ssh hev hs hc hl hcomp)
        heval hlocalised hstate hcode hlocals hcompile)
    (fun operator arguments ih => by
      intro value expressions shape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_op state context targetState operator arguments value
        expressions shape
        (fun e he v es sh hev hl hc => ih e he v es sh hev hstate hcode hlocals hl hc)
        heval hlocalised hcompile)
    (fun operator arguments ih => by
      intro value expressions shape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_panop state context targetState operator arguments value
        expressions shape
        (fun e he v es sh hev hl hc => ih e he v es sh hev hstate hcode hlocals hl hc)
        heval hlocalised hcompile)
    (fun operator left right ihleft ihright => by
      intro value expressions shape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_cmp state context targetState operator left right value
        expressions shape
        (fun sv ses ssh hev hs hc hl hcomp => ihleft sv ses ssh hev hs hc hl hcomp)
        (fun sv ses ssh hev hs hc hl hcomp => ihright sv ses ssh hev hs hc hl hcomp)
        heval hlocalised hstate hcode hlocals hcompile)
    (fun operator left right ihleft ihright => by
      intro value expressions shape heval hstate hcode hlocals hlocalised hcompile
      exact compileExpValRelHOL_shift state context targetState operator left right value
        expressions shape
        (fun sv ses ssh hev hs hc hl hcomp => ihleft sv ses ssh hev hs hc hl hcomp)
        (fun sv ses ssh hev hs hc hl hcomp => ihright sv ses ssh hev hs hc hl hcomp)
        heval hlocalised hstate hcode hlocals hcompile)
    (fun value expressions shape heval hstate _hcode _hlocals _hlocalised hcompile =>
        compileExpValRelHOL_baseAddr state context targetState value expressions shape
          heval hstate hcompile)
    (fun value expressions shape heval hstate _hcode _hlocals _hlocalised hcompile =>
        compileExpValRelHOL_topAddr state context targetState value expressions shape
          heval hstate hcompile)
    (fun value expressions shape heval _hstate _hcode _hlocals _hlocalised hcompile =>
        compileExpValRelHOL_bytesInWord state context targetState value expressions shape
          heval hcompile)
    (fun _e he => by simp at he)
    (fun head tail ihhead ihtail e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact ihhead
      · exact ihtail e he)
    (fun _p hp => by simp at hp)
    (fun head tail ihhead ihtail p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ihhead
      · exact ihtail p hp)
    (fun _fst _snd ih => ih)


end Flapjack
