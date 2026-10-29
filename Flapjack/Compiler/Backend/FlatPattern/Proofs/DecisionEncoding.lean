import Flapjack.Compiler.Backend.PatternSemantics.Semantics
import Flapjack.Compiler.Backend.FlatPattern.Proofs.NaiveMatch

/-! Encoding of flat values and references for decision-tree simulation.
The source evaluator and carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (storeLookup)

mutual
/-- Project flat values into the pattern compiler's abstract value domain. -/
def encodeValue : FlatSem.Value → PatternSemantics.Term
  | .litv lit => .litv lit
  | .conv stamp values => .term (stamp.map Prod.fst) (encodeValues values)
  | .loc _ index => .refPtr index
  | _ => .other
termination_by value => sizeOf value

/-- Encode constructor fields in their original order. -/
def encodeValues : List FlatSem.Value → List PatternSemantics.Term
  | [] => []
  | value :: values => encodeValue value :: encodeValues values
termination_by values => sizeOf values
end

/-- The auxiliary list traversal agrees with mapping the value encoding. -/
theorem encodeValues_eq_map (values : List FlatSem.Value) : encodeValues values = values.map encodeValue := by
  induction values with
  | nil => simp [encodeValues]
  | cons value values ih => simp [encodeValues, ih]

/-- A finite map containing exactly the reference-valued entries of a flat
store. The map's support is bounded by the source store length. -/
def encodeRefs {C F : Type} (state : FlatSem.State C F) : HolFiniteMapExact Nat PatternSemantics.Term where
  lookup index := match storeLookup index state.refs with
    | some (.refv value) => some (encodeValue value)
    | _ => none
  finiteSupport := by
    refine ⟨List.range state.refs.length, ?_⟩
    intro index present
    apply List.mem_range.mpr
    by_cases inside : index < state.refs.length
    · exact inside
    · have absent : storeLookup index state.refs = none := by
        apply List.getElem?_eq_none_iff.mpr
        omega
      simp [absent] at present

/-- Encoded reference lookup agrees with the original flat store lookup. -/
theorem encodeRefs_lookup {C F : Type} (state : FlatSem.State C F) (index : Nat) :
    (encodeRefs state).lookup index = match storeLookup index state.refs with
      | some (.refv value) => some (encodeValue value)
      | _ => none := rfl

/-- Following an encoded position can be replayed by evaluating the generated
flat projections, yielding a value with the same encoding. -/
theorem decodePos_simulation {C F : Type} (trace : BackendCommon.Tra)
    (state : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value)
    (position : PatternCommon.Position) (expression : FlatLang.Exp) (value : FlatSem.Value)
    (encoded : PatternSemantics.Term)
    (selected : PatternSemantics.appPos (encodeRefs state) position (encodeValue value) = some encoded)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    ∃ result, encoded = encodeValue result ∧
      FlatSem.evaluate env state [decodePos trace expression position] = (state, .val [result]) := by
  induction position generalizing expression value with
  | emptyPos =>
    simp [PatternSemantics.appPos] at selected
    subst encoded
    exact ⟨value, rfl, by simpa [decodePos] using pure⟩
  | pos index rest ih =>
    cases value with
    | litv _ | closure _ _ _ | recclosure _ _ _ | vectorv _ =>
      simp [encodeValue, PatternSemantics.appPos] at selected
    | conv stamp fields =>
      cases found : fields[index]? with
      | none =>
        simp [encodeValue, encodeValues_eq_map, PatternSemantics.appPos, List.getElem?_map, found] at selected
      | some field =>
        have next : PatternSemantics.appPos (encodeRefs state) rest (encodeValue field) = some encoded := by
          simpa [encodeValue, encodeValues_eq_map, PatternSemantics.appPos, List.getElem?_map, found] using selected
        have projected := evaluate_con_projection trace expression env state stamp fields index field pure found
        simpa [decodePos] using ih (.app trace (.el index) [expression]) field next projected
    | loc flag address =>
      cases index with
      | succ _ => simp [encodeValue, PatternSemantics.appPos] at selected
      | zero =>
        cases found : storeLookup address state.refs with
        | none => simp [encodeValue, PatternSemantics.appPos, encodeRefs_lookup, found] at selected
        | some entry =>
          cases entry with
          | w8array _ | varray _ | thunk _ _ =>
            simp [encodeValue, PatternSemantics.appPos, encodeRefs_lookup, found] at selected
          | refv contents =>
            have next : PatternSemantics.appPos (encodeRefs state) rest (encodeValue contents) = some encoded := by
              simpa [encodeValue, PatternSemantics.appPos, encodeRefs_lookup, found] using selected
            have projected := evaluate_ref_projection trace expression env state flag address contents pure found
            simpa [decodePos] using ih (.app trace (.el 0) [expression]) contents next projected

/-- A successful abstract atomic test is reproduced by its decoded flat
expression on a purely evaluated value. -/
theorem decodeTest_simulation {C F : Type} (trace : BackendCommon.Tra)
    (state : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value)
    (test : PatternSemantics.DTest) (expression : FlatLang.Exp) (value : FlatSem.Value) (answer : Bool)
    (tested : PatternSemantics.dtTest test (encodeValue value) = some answer)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    FlatSem.evaluate env state [decodeTest trace test expression] = (state, .val [FlatSem.boolValue answer]) := by
  cases test with
  | tagLenEq tag length =>
    cases value with
    | litv _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
      simp [encodeValue, PatternSemantics.dtTest] at tested
    | conv stamp fields =>
      cases stamp with
      | none => simp [encodeValue, PatternSemantics.dtTest] at tested
      | some tagged =>
        obtain ⟨actual, typeId⟩ := tagged
        have result : (tag == actual && length == fields.length) = answer := by
          simpa [encodeValue, encodeValues_eq_map, PatternSemantics.dtTest] using tested
        have guard := evaluate_tagLenEq trace expression env state tag actual typeId length fields pure
        have equalBool : (actual == tag && fields.length == length) = answer := by
          have tagSym : (actual == tag) = (tag == actual) := by
            apply Bool.eq_iff_iff.mpr
            simp only [beq_iff_eq]
            exact eq_comm
          have lenSym : (fields.length == length) = (length == fields.length) := by
            apply Bool.eq_iff_iff.mpr
            simp only [beq_iff_eq]
            exact eq_comm
          simpa only [tagSym, lenSym] using result
        simpa [decodeTest, equalBool] using guard
  | litEq lit =>
    cases value with
    | conv _ _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
      simp [encodeValue, PatternSemantics.dtTest] at tested
    | litv actual =>
      by_cases sameType : Flapjack.SemanticPrimitivesHOL.litSameType lit actual = true
      · have result : decide (lit = actual) = answer := by
          simpa [encodeValue, PatternSemantics.dtTest, sameType] using tested
        have otherType : Flapjack.SemanticPrimitivesHOL.litSameType actual lit = true := by
          simpa [litSameType_symm actual lit] using sameType
        have guard := evaluate_literal_equality trace expression env state actual lit pure otherType
        have equalBool : decide (actual = lit) = answer := by
          simpa [eq_comm] using result
        simpa [decodeTest, equalBool] using guard
      · simp [encodeValue, PatternSemantics.dtTest, sameType] at tested

/-- Comparing a pure Boolean expression to false implements Boolean negation. -/
theorem evaluate_bool_negation {C F : Type} (trace : BackendCommon.Tra)
    (state : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value)
    (expression : FlatLang.Exp) (value : Bool)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [FlatSem.boolValue value])) :
    FlatSem.evaluate env state [.app trace (.src .equality) [expression, FlatLang.mkBool trace false]] =
      (state, .val [FlatSem.boolValue (!value)]) := by
  cases value <;> simp [FlatSem.evaluate, pure, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp,
    FlatSem.doAppNumeric, FlatSem.doEq, FlatSem.doEqList, FlatSem.boolValue, FlatSem.ctorSameType,
    FlatLang.mkBool, FlatLang.boolId, BackendCommon.boolToTag, BackendCommon.trueTag, BackendCommon.falseTag]

/-- A successful abstract guard evaluates to the same Boolean after decoding
to flat expressions, including short-circuiting conjunction and disjunction. -/
theorem decodeGuard_simulation {C F : Type} (trace : BackendCommon.Tra)
    (state : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value)
    (guard : PatternSemantics.DGuard) (expression : FlatLang.Exp) (value : FlatSem.Value) (answer : Bool)
    (tested : PatternSemantics.dtEvalGuard (encodeRefs state) (encodeValue value) guard = some answer)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    FlatSem.evaluate env state [decodeGuard trace expression guard] = (state, .val [FlatSem.boolValue answer]) := by
  induction guard generalizing answer with
  | true_ =>
    simp [PatternSemantics.dtEvalGuard] at tested
    subst answer
    simpa [decodeGuard] using evaluate_bool trace true env state
  | posTest position test =>
    cases selected : PatternSemantics.appPos (encodeRefs state) position (encodeValue value) with
    | none => simp [PatternSemantics.dtEvalGuard, selected] at tested
    | some encoded =>
      have testResult : PatternSemantics.dtTest test encoded = some answer := by
        simpa [PatternSemantics.dtEvalGuard, selected] using tested
      obtain ⟨field, encoding, fieldPure⟩ := decodePos_simulation trace state env position expression value encoded selected pure
      subst encoded
      simpa [decodeGuard] using decodeTest_simulation trace state env test (decodePos trace expression position)
        field answer testResult fieldPure
  | not guard ih =>
    cases guardResult : PatternSemantics.dtEvalGuard (encodeRefs state) (encodeValue value) guard with
    | none => simp [PatternSemantics.dtEvalGuard, guardResult] at tested
    | some b =>
      have out : (!b) = answer := by
        simpa only [PatternSemantics.dtEvalGuard, guardResult, Option.map_some, Option.some.injEq] using tested
      subst answer
      have inner := ih b guardResult
      simpa [decodeGuard] using evaluate_bool_negation trace state env (decodeGuard trace expression guard) b inner
  | conj left right ihLeft ihRight =>
    cases leftResult : PatternSemantics.dtEvalGuard (encodeRefs state) (encodeValue value) left with
    | none => simp [PatternSemantics.dtEvalGuard, leftResult] at tested
    | some b =>
      cases b with
      | false =>
        simp [PatternSemantics.dtEvalGuard, leftResult] at tested
        subst answer
        have guardPure := ihLeft false leftResult
        have branch := evaluate_if_pure_bool trace (decodeGuard trace expression left) (decodeGuard trace expression right)
          (FlatLang.mkBool trace false) false env state guardPure
        simpa [decodeGuard, evaluate_smartIf, branch] using evaluate_bool trace false env state
      | true =>
        have rightResult : PatternSemantics.dtEvalGuard (encodeRefs state) (encodeValue value) right = some answer := by
          simpa [PatternSemantics.dtEvalGuard, leftResult] using tested
        have guardPure := ihLeft true leftResult
        have branch := evaluate_if_pure_bool trace (decodeGuard trace expression left) (decodeGuard trace expression right)
          (FlatLang.mkBool trace false) true env state guardPure
        simpa [decodeGuard, evaluate_smartIf, branch] using ihRight answer rightResult
  | disj left right ihLeft ihRight =>
    cases leftResult : PatternSemantics.dtEvalGuard (encodeRefs state) (encodeValue value) left with
    | none => simp [PatternSemantics.dtEvalGuard, leftResult] at tested
    | some b =>
      cases b with
      | false =>
        have rightResult : PatternSemantics.dtEvalGuard (encodeRefs state) (encodeValue value) right = some answer := by
          simpa [PatternSemantics.dtEvalGuard, leftResult] using tested
        have guardPure := ihLeft false leftResult
        have branch := evaluate_if_pure_bool trace (decodeGuard trace expression left) (FlatLang.mkBool trace true)
          (decodeGuard trace expression right) false env state guardPure
        simpa [decodeGuard, evaluate_smartIf, branch] using ihRight answer rightResult
      | true =>
        simp [PatternSemantics.dtEvalGuard, leftResult] at tested
        subst answer
        have guardPure := ihLeft true leftResult
        have branch := evaluate_if_pure_bool trace (decodeGuard trace expression left) (FlatLang.mkBool trace true)
          (decodeGuard trace expression right) true env state guardPure
        simpa [decodeGuard, evaluate_smartIf, branch] using evaluate_bool trace true env state

/-- Guard simplification preserves every successful abstract guard outcome. -/
theorem simpGuard_preserves (refs : HolFiniteMapExact Nat PatternSemantics.Term)
    (value : PatternSemantics.Term) (guard : PatternSemantics.DGuard) (answer : Bool)
    (tested : PatternSemantics.dtEvalGuard refs value guard = some answer) :
    PatternSemantics.dtEvalGuard refs value (simpGuard guard) = some answer := by
  induction guard generalizing answer with
  | true_ => simpa [simpGuard] using tested
  | posTest position test => simpa [simpGuard] using tested
  | not guard ih =>
    cases eval : PatternSemantics.dtEvalGuard refs value guard with
    | none => simp [PatternSemantics.dtEvalGuard, eval] at tested
    | some b =>
      have simplified := ih b eval
      cases b <;> simp [PatternSemantics.dtEvalGuard, eval] at tested <;> subst answer
      all_goals cases h : simpGuard guard <;> simp_all [simpGuard, PatternSemantics.dtEvalGuard]
      all_goals rename_i child
      all_goals cases child <;> simp_all [PatternSemantics.dtEvalGuard]
  | conj left right ihLeft ihRight =>
    cases leftEval : PatternSemantics.dtEvalGuard refs value left with
    | none => simp [PatternSemantics.dtEvalGuard, leftEval] at tested
    | some b =>
      have leftSimple := ihLeft b leftEval
      cases b with
      | false =>
        simp [PatternSemantics.dtEvalGuard, leftEval] at tested
        subst answer
        simp only [simpGuard]
        split
        · simp [PatternSemantics.dtEvalGuard]
        · split
          · rename_i h
            rw [h] at leftSimple
            simp [PatternSemantics.dtEvalGuard] at leftSimple
          · split
            · exact leftSimple
            · simp [PatternSemantics.dtEvalGuard, leftSimple]
      | true =>
        have rightEval : PatternSemantics.dtEvalGuard refs value right = some answer := by
          simpa [PatternSemantics.dtEvalGuard, leftEval] using tested
        have rightSimple := ihRight answer rightEval
        simp only [simpGuard]
        split
        · rename_i h
          rcases h with h | h <;> simp_all [PatternSemantics.dtEvalGuard]
        · split
          · exact rightSimple
          · split
            · rename_i h
              rw [h] at rightSimple
              simp [PatternSemantics.dtEvalGuard] at rightSimple
              subst answer
              exact leftSimple
            · simp [PatternSemantics.dtEvalGuard, leftSimple, rightSimple]

  | disj left right ihLeft ihRight =>
    cases leftEval : PatternSemantics.dtEvalGuard refs value left with
    | none => simp [PatternSemantics.dtEvalGuard, leftEval] at tested
    | some b =>
      have leftSimple := ihLeft b leftEval
      cases b with
      | true =>
        simp [PatternSemantics.dtEvalGuard, leftEval] at tested
        subst answer
        simp only [simpGuard]
        split
        · simp [PatternSemantics.dtEvalGuard]
        · split
          · rename_i h
            rw [h] at leftSimple
            simp [PatternSemantics.dtEvalGuard] at leftSimple
          · split
            · exact leftSimple
            · simp [PatternSemantics.dtEvalGuard, leftSimple]
      | false =>
        have rightEval : PatternSemantics.dtEvalGuard refs value right = some answer := by
          simpa [PatternSemantics.dtEvalGuard, leftEval] using tested
        have rightSimple := ihRight answer rightEval
        simp only [simpGuard]
        split
        · rename_i h
          rcases h with h | h <;> simp_all [PatternSemantics.dtEvalGuard]
        · split
          · exact rightSimple
          · split
            · rename_i h
              rw [h] at rightSimple
              simp [PatternSemantics.dtEvalGuard] at rightSimple
              subst answer
              exact leftSimple
            · simp [PatternSemantics.dtEvalGuard, leftSimple, rightSimple]

/-- A successfully evaluated abstract decision tree selects the same branch
after decoding to flat expressions. Type-failure trees are excluded by the
successful abstract evaluation premise. -/
theorem decodeDtree_simulation {C F : Type} (trace : BackendCommon.Tra)
    (branches : Spt FlatLang.Exp) (expression default : FlatLang.Exp)
    (state : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value)
    (value : FlatSem.Value) (tree : PatternSemantics.DTree) (result : PatternCommon.MatchResult)
    (evaluated : PatternSemantics.dtEval (encodeRefs state) (encodeValue value) tree = some result)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    FlatSem.evaluate env state [decodeDtree trace branches expression default tree] =
      FlatSem.evaluate env state [match result with
        | .success index => (sptLookup index branches).getD default
        | .failure => default] := by
  induction tree generalizing result with
  | leaf index =>
    simp [PatternSemantics.dtEval] at evaluated
    subst result
    rfl
  | fail =>
    simp [PatternSemantics.dtEval] at evaluated
    subst result
    rfl
  | typeFail => simp [PatternSemantics.dtEval] at evaluated
  | if_ guard yes no ihYes ihNo =>
    cases guardEval : PatternSemantics.dtEvalGuard (encodeRefs state) (encodeValue value) guard with
    | none => simp [PatternSemantics.dtEval, guardEval] at evaluated
    | some b =>
      have simplified := simpGuard_preserves (encodeRefs state) (encodeValue value) guard b guardEval
      have decoded := decodeGuard_simulation trace state env (simpGuard guard) expression value b simplified pure
      cases b with
      | false =>
        have noEval : PatternSemantics.dtEval (encodeRefs state) (encodeValue value) no = some result := by
          simpa [PatternSemantics.dtEval, guardEval] using evaluated
        have noCorrect := ihNo result noEval
        by_cases isTrue : simpGuard guard = .true_
        · rw [isTrue] at simplified
          simp [PatternSemantics.dtEvalGuard] at simplified
        · by_cases isFalse : simpGuard guard = .not .true_
          · cases result <;> simpa [decodeDtree, isTrue, isFalse] using noCorrect
          · have branch := evaluate_if_pure_bool trace (decodeGuard trace expression (simpGuard guard))
              (decodeDtree trace branches expression default yes) (decodeDtree trace branches expression default no)
              false env state decoded
            cases result <;> simpa [decodeDtree, isTrue, isFalse, evaluate_smartIf, branch] using noCorrect
      | true =>
        have yesEval : PatternSemantics.dtEval (encodeRefs state) (encodeValue value) yes = some result := by
          simpa [PatternSemantics.dtEval, guardEval] using evaluated
        have yesCorrect := ihYes result yesEval
        by_cases isTrue : simpGuard guard = .true_
        · cases result <;> simpa [decodeDtree, isTrue] using yesCorrect
        · by_cases isFalse : simpGuard guard = .not .true_
          · rw [isFalse] at simplified
            simp [PatternSemantics.dtEvalGuard] at simplified
          · have branch := evaluate_if_pure_bool trace (decodeGuard trace expression (simpGuard guard))
              (decodeDtree trace branches expression default yes) (decodeDtree trace branches expression default no)
              true env state decoded
            cases result <;> simpa [decodeDtree, isTrue, isFalse, evaluate_smartIf, branch] using yesCorrect

end Flapjack.Compiler.Backend.FlatPattern
