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

end Flapjack.Compiler.Backend.FlatPattern
