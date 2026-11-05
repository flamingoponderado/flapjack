import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.CrepSem.LookupCode
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.MulConst
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect

/-!
# Crep arithmetic proof-script state updates

The `mapc` overload and its `FLOOKUP_mapc` equation are local to
`crep_arithProofScript.sml:109`. They live under the `CrepArith` counterpart,
while the carrier itself remains in `Semantics.CrepSem.HOLState`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-! The canonical finite-map carrier is owned by the Crep semantics module.
This same-module re-export makes its existing kernel-checked roundtrip
available to finite-support qualifiers in the CrepArith counterpart, without
declaring another state carrier. -/
namespace CrepArithSimpExpCorrectWitnesses

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    {ffiState : Type} :
    (∀ (state : CrepSemBroadState width ffiState) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width ffiState,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepArithSimpExpCorrectWitnesses

/-- HOL's local `mapc f` state update, using `FMAP_MAP2` on the code map.
Declared as an `abbrev` so that projection equations (and the shared-memory
domain decision procedure) reduce during type class synthesis, exactly as for
the clock-shift abbreviation `crepStateAddClock`. -/
abbrev CrepSemHOLState.mapc {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  { state with code := state.code.map2 f }

@[simp] theorem CrepSemHOLState.FLOOKUP_mapc {width : Nat} [NeZero width]
    {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (name : MlString) :
    (state.mapc f).code.lookup name =
      (state.code.lookup name).map (fun entry => f (name, entry)) := rfl

@[simp] theorem CrepSemHOLState.toExpressionEvaluatorState_mapc
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) :
    (state.mapc f).toExpressionEvaluatorState =
      state.toExpressionEvaluatorState := by
  rfl

@[simp] theorem CrepSemHOLState.toBitVecEvaluatorState_mapc
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) :
    (state.mapc f).toBitVecEvaluatorState = state.toBitVecEvaluatorState := rfl

/-- HOL's proof-script-local `mapc` update on an arbitrary-index finite state.
This only uses the finite-map `FMAP_MAP2` encoding; it makes no claim about
the code-entry representation. -/
def CrepSemHOLFiniteState.mapc {ι β σ : Type}
    (f : MlString × β → β) (state : CrepSemHOLFiniteState ι β σ) :
    CrepSemHOLFiniteState ι β σ :=
  { state with code := state.code.map2 f }

@[simp] theorem CrepSemHOLFiniteState.toSourceEvaluatorState_mapc
    {ι β σ : Type} (f : MlString × β → β)
    (state : CrepSemHOLFiniteState ι β σ) :
    (state.mapc f).toSourceEvaluatorState = state.toSourceEvaluatorState := rfl

/-- Changing only the HOL code map cannot alter expression evaluation after
projection into the source evaluator. This is Flapjack support for the
`simp_exp_correct1` dependency; the evaluator correspondence to native HOL
remains unproved. -/
theorem evalCrepHolFiniteWordSourceExp_mapc_projection
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        (state.mapc f).toExpressionEvaluatorState expression =
      evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        state.toExpressionEvaluatorState expression := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]


/-- Var case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It
    retains the successful-evaluation premise, polymorphic unused result
    binder, full `Option (word_lab)` result and proof-script-local code-only
    `mapc` update. The same-module finite-map witness above re-exports the
    existing `CrepSemHOLState` roundtrip; it does not declare a second carrier. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeVarCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (name : Nat)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.var name) ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.var name)) =
      evalCrepSemHOLExp state (.var name) := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- Const case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It
    preserves the same premise and polymorphic unused result binder, plus the
    complete optional `word_lab` conclusion; a constant evaluates to the same
    word after the code-only `mapc` update. The state finite-map fields use the
    reviewed canonical finite-support carrier, and words use the reviewed
    positive-width `BitVec` model. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeConstCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (value : BitVec width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.const value) ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.const value)) =
      evalCrepSemHOLExp state (.const value) := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- LoadGlob case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    HOL `eval_def` reads the globals finite map, while the proof-script-local
    `mapc` update changes only code; `simp_exp` leaves LoadGlob unchanged.
    The theorem keeps the unused polymorphic result binder, successful
    evaluation premise, and complete optional `word_lab` result. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeLoadGlobCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (address : BitVec 5)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.loadGlob address) ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.loadGlob address)) =
      evalCrepSemHOLExp state (.loadGlob address) := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- BaseAddr case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    HOL `eval_def` reads `state.base_addr`, `simp_exp` leaves BaseAddr
    unchanged, and the proof-script-local `mapc` update changes only code.
    The theorem preserves the unused polymorphic result binder, successful
    evaluation premise, and complete optional `word_lab` result. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeBaseAddrCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state .baseAddr ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL .baseAddr) =
      evalCrepSemHOLExp state .baseAddr := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- TopAddr case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    HOL `eval_def` reads `state.top_addr`, `simp_exp` leaves TopAddr
    unchanged, and the proof-script-local `mapc` update changes only code.
    The theorem preserves the unused polymorphic result binder, successful
    evaluation premise, and complete optional `word_lab` result. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeTopAddrCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state .topAddr ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL .topAddr) =
      evalCrepSemHOLExp state .topAddr := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- Load case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    The recursive premise is at the same state as the Load evaluation, as in
    HOL's `eval_ind`. The successful full Load evaluation
    premise is retained; code-only `mapc` preserves evaluation of the address,
    and the complete optional `word_lab` result is unchanged. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeLoadCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (address : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.load address) ≠ none)
    (ih : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state address ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL address) =
        evalCrepSemHOLExp state address) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.load address)) =
      evalCrepSemHOLExp state (.load address) := by
  have hAddress : evalCrepSemHOLExp state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hAddressEval := ih _result hAddress
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hAddressEval]

/-- Load32 case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    The recursive premise uses the current state, as in HOL `eval_ind`, and
    retains the unused result binder. The successful full Load32 premise,
    exact code-only `mapc`, and complete optional `word_lab` result are kept. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeLoad32Case
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (address : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.load32 address) ≠ none)
    (ih : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state address ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL address) =
        evalCrepSemHOLExp state address) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.load32 address)) =
      evalCrepSemHOLExp state (.load32 address) := by
  have hAddress : evalCrepSemHOLExp state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hAddressEval := ih _result hAddress
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hAddressEval]

/-- LoadByte case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    Its recursive premise uses the current state, as in HOL `eval_ind`, and
    retains the unused result binder. The full successful-load premise,
    code-only `mapc`, and complete optional `word_lab` result are retained. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeLoadByteCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (address : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.loadByte address) ≠ none)
    (ih : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state address ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL address) =
        evalCrepSemHOLExp state address) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.loadByte address)) =
      evalCrepSemHOLExp state (.loadByte address) := by
  have hAddress : evalCrepSemHOLExp state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hAddressEval := ih _result hAddress
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hAddressEval]

/-- Cmp case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    Both child induction hypotheses use the current state, as in HOL
    `eval_ind`, while retaining the unused result binder. The successful
    full-Cmp premise, code-only `mapc`, and complete optional result remain. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeCmpCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (operator : Cmp)
    (left right : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.cmp operator left right) ≠ none)
    (ihLeft : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state left ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL left) = evalCrepSemHOLExp state left)
    (ihRight : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state right ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL right) = evalCrepSemHOLExp state right) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.cmp operator left right)) =
      evalCrepSemHOLExp state (.cmp operator left right) := by
  have hLeft : evalCrepSemHOLExp state left ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hRight : evalCrepSemHOLExp state right ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hLeftEval := ihLeft _result hLeft
  have hRightEval := ihRight _result hRight
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hLeftEval, hRightEval]

/-- Shift case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    Both child induction hypotheses use the current state, as in HOL
    `eval_ind`, while retaining the unused result binder. The successful
    full-Shift premise, code-only `mapc`, and complete optional result remain. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeShiftCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (operator : Shift)
    (left right : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.shift operator left right) ≠ none)
    (ihLeft : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state left ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL left) = evalCrepSemHOLExp state left)
    (ihRight : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state right ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL right) = evalCrepSemHOLExp state right) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.shift operator left right)) =
      evalCrepSemHOLExp state (.shift operator left right) := by
  have hLeft : evalCrepSemHOLExp state left ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hRight : evalCrepSemHOLExp state right ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hLeftEval := ihLeft _result hLeft
  have hRightEval := ihRight _result hRight
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hLeftEval, hRightEval]

/-- Op case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`), where
    `simp_exp (Op bop exps) = Op bop (MAP simp_exp exps)`
    (`crep_arithScript.sml:75`).  The operand-list induction hypothesis is
    HOL `eval_ind`'s Op premise at the current state (`∀e. MEM e es ⇒ P s e`)
    and keeps HOL's unused result binder.  The successful full-expression
    premise, code-only `mapc`, and complete optional `word_lab` result are
    retained; the proof lifts the per-operand equalities through `OPT_MMAP`
    with `OPT_MMAP_EQ_SOME_MONO` (`optMmapEqSomeMono`), as HOL does. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeOpCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (operator : BinOp)
    (expressions : List (CrepExpHOL width))
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.op operator expressions) ≠ none)
    (ih : ∀ (child : CrepExpHOL width), child ∈ expressions →
      ∀ {resultType : Type} (_result : resultType),
        evalCrepSemHOLExp state child ≠ none →
        evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
            (crepSimpExpHOL child) = evalCrepSemHOLExp state child) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.op operator expressions)) =
      evalCrepSemHOLExp state (.op operator expressions) := by
  have hArgsSome : expressions.mapM (evalCrepSemHOLExp state) ≠ none := by
    intro hNone
    apply _h
    rw [evalCrepSemHOLExp.eq_7, hNone]
    rfl
  obtain ⟨values, hArgs⟩ := Option.ne_none_iff_exists'.mp hArgsSome
  have hSimplifiedArgs := optMmapEqSomeMono
    (evalCrepSemHOLExp state)
    (fun child => evalCrepSemHOLExp
      (CrepSemHOLState.mapc update state) (crepSimpExpHOL child))
    expressions values hArgs
    (by
      intro child value hmem hValue
      have hChildIH := ih child hmem _result (by rw [hValue]; simp)
      rw [hChildIH, hValue])
  have hSimplifiedArgs' :
      (expressions.map crepSimpExpHOL).mapM
          (evalCrepSemHOLExp (CrepSemHOLState.mapc update state)) = some values := by
    rw [List.mapM_map]
    exact hSimplifiedArgs
  have hSimplified :
      crepSimpExpHOL (.op operator expressions) =
        .op operator (expressions.map crepSimpExpHOL) := by
    simp only [crepSimpExpHOL]
  rw [hSimplified, evalCrepSemHOLExp.eq_7, evalCrepSemHOLExp.eq_7,
    hSimplifiedArgs', hArgs]

/-- Flapjack-only inversion lemma for the exact `dest_const` function. HOL's
    proof script invokes the analogous standard HOL equality reasoning
    directly; this local theorem exposes the constructor inversion needed by
    Lean's indexed Crep carrier. -/
private theorem crepDestConstHOL_eq_some_implies {width : Nat} [NeZero width]
    {expression : CrepExpHOL width} {value : BitVec width}
    (h : crepDestConstHOL expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConstHOL]

/-- Flapjack-only equation view for the Crepop/Mul recursive branch. The HOL
    simplifier equation is generated by its function definition rather than a
    separate HOL declaration; this helper uses Lean's generated equation
    theorem to expose the exact branch without unfolding recursive children. -/
private theorem crepSimpExpHOL_mul_eq {width : Nat} [NeZero width]
    (left right : CrepExpHOL width) :
    crepSimpExpHOL (.crepOp .mul [left, right]) =
      match crepDestConstHOL (crepSimpExpHOL left),
          crepDestConstHOL (crepSimpExpHOL right) with
      | some first, some second => .const (first * second)
      | some constant, none => crepMulConstHOL (crepSimpExpHOL right) constant
      | none, some constant => crepMulConstHOL (crepSimpExpHOL left) constant
      | none, none => .crepOp .mul [crepSimpExpHOL left, crepSimpExpHOL right] := by
  have hMap : List.map crepSimpExpHOL [left, right] =
      [crepSimpExpHOL left, crepSimpExpHOL right] := rfl
  rw [crepSimpExpHOL.eq_1 [left, right]
    (crepSimpExpHOL left) (crepSimpExpHOL right) hMap]
  rfl

/-- Crepop case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    The operand-list induction hypothesis is fixed to the current state and
    keeps HOL's unused result binder. The successful full-expression premise,
    code-only `mapc`, and complete optional `word_lab` result are retained;
    the Mul constant-fold and `mul_const` cases use the exact arithmetic
    helper `eval_mul_const`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeCrepopCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (operator : CrepOp)
    (expressions : List (CrepExpHOL width))
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.crepOp operator expressions) ≠ none)
    (ih : ∀ (child : CrepExpHOL width), child ∈ expressions →
      ∀ {resultType : Type} (_result : resultType),
        evalCrepSemHOLExp state child ≠ none →
        evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
            (crepSimpExpHOL child) = evalCrepSemHOLExp state child) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.crepOp operator expressions)) =
      evalCrepSemHOLExp state (.crepOp operator expressions) := by
  cases operator with
  | mul =>
    cases expressions with
    | nil =>
      have hEval : evalCrepSemHOLExp state (.crepOp .mul []) = none := by
        simp [evalCrepSemHOLExp, crepOpCrepWord]
      exact (False.elim (_h hEval))
    | cons left rest =>
      cases rest with
      | nil =>
        have hEval : evalCrepSemHOLExp state (.crepOp .mul [left]) = none := by
          cases hLeft : evalCrepSemHOLExp state left <;>
            simp [evalCrepSemHOLExp, hLeft, crepOpCrepWord]
        exact (False.elim (_h hEval))
      | cons right tail =>
        cases tail with
        | cons extra more =>
          have hEval :
              evalCrepSemHOLExp state (.crepOp .mul (left :: right :: extra :: more)) = none := by
            cases hLeft : evalCrepSemHOLExp state left <;>
              cases hRight : evalCrepSemHOLExp state right <;>
              cases hExtra : evalCrepSemHOLExp state extra <;>
              cases hMore : more.mapM (evalCrepSemHOLExp state) <;>
                simp [evalCrepSemHOLExp, hLeft, hRight, hExtra, hMore, crepOpCrepWord]
          exact (False.elim (_h hEval))
        | nil =>
          have hLeft : evalCrepSemHOLExp state left ≠ none := by
            intro hNone
            apply _h
            simp [evalCrepSemHOLExp, hNone]
          have hRight : evalCrepSemHOLExp state right ≠ none := by
            intro hNone
            apply _h
            simp [evalCrepSemHOLExp, hNone]
          obtain ⟨leftResult, hLeftEval⟩ := Option.ne_none_iff_exists'.mp hLeft
          obtain ⟨rightResult, hRightEval⟩ := Option.ne_none_iff_exists'.mp hRight
          cases leftResult with
          | word leftWord =>
            cases rightResult with
            | word rightWord =>
              have hLeftIH := ih left (by simp) _result hLeft
              have hRightIH := ih right (by simp) _result hRight
              have hLeftMapped :
                  evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
                    (crepSimpExpHOL left) = some (.word leftWord) := by
                rw [hLeftIH, hLeftEval]
              have hRightMapped :
                  evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
                    (crepSimpExpHOL right) = some (.word rightWord) := by
                rw [hRightIH, hRightEval]
              have hOriginal :
                  evalCrepSemHOLExp state (.crepOp .mul [left, right]) =
                    some (.word (leftWord * rightWord)) := by
                simp [evalCrepSemHOLExp, hLeftEval, hRightEval, crepOpCrepWord]
              cases hLeftConst : crepDestConstHOL (crepSimpExpHOL left) with
              | none =>
                cases hRightConst : crepDestConstHOL (crepSimpExpHOL right) with
                | none =>
                  have hSimplified :
                      crepSimpExpHOL (.crepOp .mul [left, right]) =
                        .crepOp .mul [crepSimpExpHOL left, crepSimpExpHOL right] := by
                    rw [crepSimpExpHOL_mul_eq, hLeftConst, hRightConst]
                  rw [hSimplified]
                  have hOriginalArgs :
                      [left, right].mapM (evalCrepSemHOLExp state) =
                        some [.word leftWord, .word rightWord] := by
                    simp [hLeftEval, hRightEval]
                  have hSimplifiedArgs := optMmapEqSomeMono
                    (evalCrepSemHOLExp state)
                    (fun child => evalCrepSemHOLExp
                      (CrepSemHOLState.mapc update state) (crepSimpExpHOL child))
                    [left, right] [.word leftWord, .word rightWord] hOriginalArgs
                    (by
                      intro child value hmem hValue
                      have hChildIH := ih child hmem _result (by rw [hValue]; simp)
                      rw [hChildIH, hValue])
                  have hSimplifiedArgs' :
                      [crepSimpExpHOL left, crepSimpExpHOL right].mapM
                          (evalCrepSemHOLExp (CrepSemHOLState.mapc update state)) =
                        some [.word leftWord, .word rightWord] := by
                    simpa using hSimplifiedArgs
                  rw [evalCrepSemHOLExp.eq_8, evalCrepSemHOLExp.eq_8,
                    hSimplifiedArgs', hOriginalArgs]
                | some rightConst =>
                  have hRightConstExp :
                      crepSimpExpHOL right = .const rightConst := by
                    exact crepDestConstHOL_eq_some_implies hRightConst
                  have hRightValue : rightConst = rightWord := by
                    have hEval := hRightMapped
                    rw [hRightConstExp, evalCrepSemHOLExp] at hEval
                    injection hEval with hValue
                    cases hValue
                    rfl
                  have hMulConst := crepEval_mul_const
                    (CrepSemHOLState.mapc update state)
                    (crepSimpExpHOL left) leftWord rightConst hLeftMapped
                  have hSimplified :
                      crepSimpExpHOL (.crepOp .mul [left, right]) =
                        crepMulConstHOL (crepSimpExpHOL left) rightConst := by
                    rw [crepSimpExpHOL_mul_eq, hLeftConst, hRightConst]
                  rw [hSimplified, hMulConst, hOriginal]
                  simp [hRightValue]
              | some leftConst =>
                cases hRightConst : crepDestConstHOL (crepSimpExpHOL right) with
                | none =>
                  have hLeftConstExp :
                      crepSimpExpHOL left = .const leftConst := by
                    exact crepDestConstHOL_eq_some_implies hLeftConst
                  have hLeftValue : leftConst = leftWord := by
                    have hEval := hLeftMapped
                    rw [hLeftConstExp, evalCrepSemHOLExp] at hEval
                    injection hEval with hValue
                    cases hValue
                    rfl
                  have hMulConst := crepEval_mul_const
                    (CrepSemHOLState.mapc update state)
                    (crepSimpExpHOL right) rightWord leftConst hRightMapped
                  have hSimplified :
                      crepSimpExpHOL (.crepOp .mul [left, right]) =
                        crepMulConstHOL (crepSimpExpHOL right) leftConst := by
                    rw [crepSimpExpHOL_mul_eq, hLeftConst, hRightConst]
                  rw [hSimplified, hMulConst, hOriginal]
                  simpa [hLeftValue] using (BitVec.mul_comm rightWord leftWord)
                | some rightConst =>
                  have hLeftConstExp :
                      crepSimpExpHOL left = .const leftConst := by
                    exact crepDestConstHOL_eq_some_implies hLeftConst
                  have hRightConstExp :
                      crepSimpExpHOL right = .const rightConst := by
                    exact crepDestConstHOL_eq_some_implies hRightConst
                  have hLeftValue : leftConst = leftWord := by
                    have hEval := hLeftMapped
                    rw [hLeftConstExp, evalCrepSemHOLExp] at hEval
                    injection hEval with hValue
                    cases hValue
                    rfl
                  have hRightValue : rightConst = rightWord := by
                    have hEval := hRightMapped
                    rw [hRightConstExp, evalCrepSemHOLExp] at hEval
                    injection hEval with hValue
                    cases hValue
                    rfl
                  have hSimplified :
                      crepSimpExpHOL (.crepOp .mul [left, right]) =
                        CrepExpHOL.const (leftConst * rightConst) := by
                    rw [crepSimpExpHOL_mul_eq, hLeftConst, hRightConst]
                  rw [hSimplified]
                  rw [evalCrepSemHOLExp, hOriginal]
                  simp [hLeftValue, hRightValue]


/-! ## Assembled `simp_exp_correct1` and `simp_exp_correct`

HOL proves `simp_exp_correct1` by `ho_match_mp_tac (name_ind_cases [] eval_ind)`
(`crep_arithProofScript.sml:111-142`).  Crep's expression `eval_ind` is not
ported as a Lean declaration, so the assembly below uses structural induction
on `CrepExpHOL` (with the operand-list motive `∀ child ∈ es, P child`).  This
supplies exactly the `eval_ind` IHs, all at the fixed current state, to the
twelve tagged native case theorems above. -/

/-- Exact HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111-114`):
    `∀s exp v. crepSem$eval s exp ≠ NONE ⇒
      eval (mapc f s) (simp_exp exp) = eval s exp`, with `f` free (here the
    first explicit argument `update`) and HOL's unused, arbitrarily typed `v`.
    It is stated over the tagged native `evalCrepSemHOLExp` (`eval_def`),
    `crepSimpExpHOL` (`simp_exp_def`) and `CrepSemHOLState.mapc`, with the
    complete `Option word_lab` result and no other premise.  Assembled from the
    tagged native constructor cases (`crepSimpExpCorrect1Native*Case`).
    (HOL marks this theorem `[local]`; it is ported because `simp_exp_correct`
    and `simp_prog_correct` depend on it.) -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeHOL
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width) :
    ∀ (state : CrepSemHOLState width σ) (exp : CrepExpHOL width)
      {resultType : Type} (_v : resultType),
      evalCrepSemHOLExp state exp ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state) (crepSimpExpHOL exp) =
        evalCrepSemHOLExp state exp := by
  intro state exp
  induction exp using CrepExpHOL.rec (motive_2 := fun es => ∀ child ∈ es,
      ∀ {resultType : Type} (_v : resultType),
        evalCrepSemHOLExp state child ≠ none →
        evalCrepSemHOLExp (CrepSemHOLState.mapc update state) (crepSimpExpHOL child) =
          evalCrepSemHOLExp state child) with
  | const value =>
      intro _ v h; exact crepSimpExpCorrect1NativeConstCase update state value v h
  | var name =>
      intro _ v h; exact crepSimpExpCorrect1NativeVarCase update state name v h
  | load address ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeLoadCase update state address v h ih
  | load32 address ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeLoad32Case update state address v h ih
  | loadByte address ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeLoadByteCase update state address v h ih
  | loadGlob address =>
      intro _ v h; exact crepSimpExpCorrect1NativeLoadGlobCase update state address v h
  | op operator args ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeOpCase update state operator args v h ih
  | crepOp operator args ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeCrepopCase update state operator args v h ih
  | cmp operator left right ihLeft ihRight =>
      intro _ v h
      exact crepSimpExpCorrect1NativeCmpCase update state operator left right v h ihLeft ihRight
  | shift operator left right ihLeft ihRight =>
      intro _ v h
      exact crepSimpExpCorrect1NativeShiftCase update state operator left right v h
        ihLeft ihRight
  | baseAddr =>
      intro _ v h; exact crepSimpExpCorrect1NativeBaseAddrCase update state v h
  | topAddr =>
      intro _ v h; exact crepSimpExpCorrect1NativeTopAddrCase update state v h
  | nil =>
      rename_i hmem _ _ _
      cases hmem
  | cons head tail ihHead ihTail =>
      rename_i child hmem _ v h
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ihHead v h
      · exact ihTail child hmem v h

/-- Exact HOL `simp_exp_correct` (`crep_arithProofScript.sml:143-145`):
    `crepSem$eval s exp = SOME v ⇒ eval (mapc f s) (simp_exp exp) = SOME v`,
    with `f`, `s`, `exp`, `v` free, over the same tagged native evaluator,
    simplifier and `mapc`.  Proved from `simp_exp_correct1`, as in HOL. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrectNativeHOL
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (exp : CrepExpHOL width) (v : HolWordLab width) :
    evalCrepSemHOLExp state exp = some v →
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state) (crepSimpExpHOL exp) = some v := by
  intro h
  rw [crepSimpExpCorrect1NativeHOL update state exp v (by rw [h]; simp), h]

/-- Exact HOL `opt_mmap_simp_exp_correct` (`crep_arithProofScript.sml:150-152`):
    `OPT_MMAP (crepSem$eval s) es = SOME vs ⇒
      OPT_MMAP (eval (mapc f s)) (MAP simp_exp es) = SOME vs`, with `f s es vs`
    free.  HOL `OPT_MMAP` is `List.mapM`, over the tagged native
    `evalCrepSemHOLExp`, `crepSimpExpHOL` and `CrepSemHOLState.mapc`.  Proved
    from `simp_exp_correct` elementwise, as HOL does with `OPT_MMAP_CONG`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "opt_mmap_simp_exp_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepOptMmapSimpExpCorrectNativeHOL
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (es : List (CrepExpHOL width))
    (vs : List (HolWordLab width)) :
    es.mapM (evalCrepSemHOLExp state) = some vs →
    (es.map crepSimpExpHOL).mapM
        (evalCrepSemHOLExp (CrepSemHOLState.mapc update state)) = some vs := by
  intro h
  rw [List.mapM_map]
  exact optMmapEqSomeMono (evalCrepSemHOLExp state) _ es vs h
    (fun child value _ hValue =>
      crepSimpExpCorrectNativeHOL update state child value hValue)

/-- Exact HOL `lookup_code` (`crep_arithProofScript.sml:162-164`, `[local]`):
    `lookup_code (FMAP_MAP2 (\(s,n,p). (n, simp_prog p)) c) fname args len =
      OPTION_MAP (simp_prog ## I) (lookup_code c fname args len)`, with
    `c fname args len` free.  `c` is the HOL finite map `funname |-> (varname
    list # prog)` in the canonical `HolFiniteMapExact` carrier (hence the
    standalone relation-qualifier entry `c`), `FMAP_MAP2` is
    `HolFiniteMapExact.map2`, and `lookup_code` is the tagged `lookupCodeHOL`
    applied to the map's `lookup` function, the same way the tagged Crep
    evaluator reads `s.code`.  `f ## I` is `Prod.map f id`.  No premise. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "lookup_code"
  (fmap_as_finite_support_relation := [c])
  (words_as_type_indexed_bitvec)]
theorem crepArithLookupCodeNativeHOL {width : Nat} [NeZero width]
    (c : HolFiniteMapExact MlString (List Nat × CrepProgHOL width))
    (fname : MlString) (args : List (HolWordLab width)) (len : Nat) :
    lookupCodeHOL
        (c.map2 (fun (_, entry) => (entry.1, crepSimpProgHOL entry.2))).lookup fname args len =
      (lookupCodeHOL c.lookup fname args len).map (Prod.map crepSimpProgHOL id) := by
  unfold lookupCodeHOL
  simp only [FLOOKUP, HolFiniteMapExact.lookup_map2]
  cases hc : c.lookup fname with
  | none => rfl
  | some entry =>
      obtain ⟨parameters, body⟩ := entry
      simp only [Option.map_some]
      split <;> rfl

/-- The shared `mapcs` renderer `crepSimpMapcsHOL` (`SimpProgCorrect.lean`) is
    exactly the proof script's `mapcs = mapc (\(s,n,p). (n, simp_prog p))`
    over `CrepSemHOLState.mapc`. Flapjack-only, untagged. -/
theorem crepSimpMapcsHOL_eq_mapc {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    crepSimpMapcsHOL state =
      state.mapc (fun (_, entry) => (entry.1, crepSimpProgHOL entry.2)) := rfl

/-- The `lookup_code` lemma at the finite-support wrapper `lookupCodeHOLFinite`
    that the tagged Crep evaluator's Call clause uses on `(mapcs s).code`, stated
    with the shared `mapcs` renderer `crepSimpMapcsHOL`: looking up in the
    `simp_prog`-mapped code returns the simplified body with the same callee
    locals.  Flapjack-only companion of `crepArithLookupCodeNativeHOL`, untagged. -/
theorem crepArithLookupCodeHOLFinite_mapcs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (fname : MlString) (args : List (HolWordLab width)) (len : Nat) :
    lookupCodeHOLFinite (crepSimpMapcsHOL state).code.lookup fname args len =
      (lookupCodeHOLFinite state.code.lookup fname args len).map
        (Prod.map crepSimpProgHOL id) := by
  have hbase := crepArithLookupCodeNativeHOL state.code fname args len
  unfold lookupCodeHOLFinite
  split
  · rename_i hnone
    split
    · rfl
    · rename_i body locals hsome
      change lookupCodeHOL
          (state.code.map2 (fun (_, entry) => (entry.1, crepSimpProgHOL entry.2))).lookup
          fname args len = none at hnone
      rw [hbase, hsome] at hnone
      cases hnone
  · rename_i body locals hsome
    split
    · rename_i hnone
      change lookupCodeHOL
          (state.code.map2 (fun (_, entry) => (entry.1, crepSimpProgHOL entry.2))).lookup
          fname args len = some (body, locals) at hsome
      rw [hbase, hnone] at hsome
      cases hsome
    · rename_i body' locals' hsome'
      change lookupCodeHOL
          (state.code.map2 (fun (_, entry) => (entry.1, crepSimpProgHOL entry.2))).lookup
          fname args len = some (body, locals) at hsome
      rw [hbase, hsome'] at hsome
      simp only [Option.map_some, Prod.map, Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      rfl
/-! ## The proof-script-local `sh_mem_op_code`

`crep_arithProofScript.sml:173-180` proves that the proof-script-local `mapc`
code rewrite commutes with the shared-memory operation. `sh_mem_op` reads only
the locals, the shared-memory domain and the FFI, and writes only the locals
and the FFI, so the code map is untouched on both sides. The two lemmas below
are the exact `sh_mem_load`/`sh_mem_store` instances of the HOL
`Cases_on op` step; they are Flapjack-specific support with no separate HOL
original. -/

private theorem crepShMemLoadExactHOL_mapc {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) → List Nat × CrepProgHOL width)
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs]
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (h : crepShMemLoadExactHOL name address nb state = (r, s')) :
    crepShMemLoadExactHOL name address nb (state.mapc f) = (r, s'.mapc f) := by
  have hs : s' = (crepShMemLoadExactHOL name address nb state).2 := by rw [h]
  subst hs
  have hr : r = (crepShMemLoadExactHOL name address nb state).1 := by rw [h]
  subst hr
  unfold crepShMemLoadExactHOL
  simp only [CrepSemHOLState.mapc]
  split <;> (try split) <;> (try split) <;> rfl

private theorem crepShMemStoreExactHOL_mapc {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) → List Nat × CrepProgHOL width)
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs]
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (h : crepShMemStoreExactHOL name address nb state = (r, s')) :
    crepShMemStoreExactHOL name address nb (state.mapc f) = (r, s'.mapc f) := by
  have hs : s' = (crepShMemStoreExactHOL name address nb state).2 := by rw [h]
  subst hs
  have hr : r = (crepShMemStoreExactHOL name address nb state).1 := by rw [h]
  subst hr
  unfold crepShMemStoreExactHOL
  simp only [CrepSemHOLState.mapc]
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-- Exact port of HOL `sh_mem_op_code` (`crep_arithProofScript.sml:173-180`):
    the proof-script-local `mapc f` code update commutes with `sh_mem_op`. HOL
    writes the pair map as `I ## mapc f`; here it is `Prod.map id
    (CrepSemHOLState.mapc f)`. The operator/register/address/state binder order
    is HOL's `op p addr s`. The `[DecidablePred state.shMemaddrs]` argument is
    Lean's decision procedure for the shared-memory domain predicate (HOL uses
    classical decidability of `addr IN s.sh_memaddrs`), exactly as in the
    tagged `sh_mem_load_def`/`sh_mem_store_def`/`sh_mem_op_def` ports; there is
    no additional mathematical premise. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "sh_mem_op_code"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepShMemOpExactHOL_mapc {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) → List Nat × CrepProgHOL width)
    (operator : WordMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    crepShMemOpExactHOL operator name address (state.mapc f) =
      Prod.map id (CrepSemHOLState.mapc f)
        (crepShMemOpExactHOL operator name address state) := by
  cases operator <;>
    simp only [crepShMemOpExactHOL, Prod.map, id_eq] <;>
    first
    | exact crepShMemLoadExactHOL_mapc f name address 0 state _ _ rfl
    | exact crepShMemStoreExactHOL_mapc f name address 0 state _ _ rfl
    | exact crepShMemLoadExactHOL_mapc f name address 1 state _ _ rfl
    | exact crepShMemStoreExactHOL_mapc f name address 1 state _ _ rfl
    | exact crepShMemLoadExactHOL_mapc f name address 2 state _ _ rfl
    | exact crepShMemStoreExactHOL_mapc f name address 2 state _ _ rfl
    | exact crepShMemLoadExactHOL_mapc f name address 4 state _ _ rfl
    | exact crepShMemStoreExactHOL_mapc f name address 4 state _ _ rfl

end Flapjack
