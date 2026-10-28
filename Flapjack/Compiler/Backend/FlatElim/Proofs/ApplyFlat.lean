import Flapjack.Compiler.Backend.FlatElim.Proofs.ApplyMemory

/-! Flat-specific primitive cases for the elimination simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- A single Eval-free reachable value satisfies the primitive result invariants. -/
theorem primitiveResult_value_invariants (reachable : NumSet) (value : FlatSem.Value)
    (valueReachable : globalsWithin (findValueGlobals value) reachable)
    (valueSafe : valueHasEval value = false) :
    globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult (.val value))) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult (.val value))) := by
  constructor
  · simp only [findPrimitiveResultGlobals, Flapjack.EvaluateHOL.listResult, findValuesGlobals]
    rw [globalsWithin_union]
    exact ⟨valueReachable, by simp [globalsWithin, sptMem, sptDomain]⟩
  · simpa [Flapjack.Compiler.Backend.FlatProps.resultValues, Flapjack.EvaluateHOL.listResult,
      valuesNoEval] using valueSafe

/-- The flat element operation covers constructor projection and reference
reads. Both preserve the primitive simulation's original result obligations. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_el {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (index : Nat)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.el index ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.el index) [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.el index) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.el index) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | cons first rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      have firstReachable : globalsWithin (findValueGlobals first) reachable :=
        ((globalsWithin_union _ _ _).mp (by simpa [findValuesGlobals] using valuesReachable)).1
      have firstSafe : valueHasEval first = false := valuesSafe first (by simp)
      cases first <;> simp [FlatSem.doApp, FlatSem.doAppFlat] at run
      case conv stamp fields =>
        cases found : fields[index]? with
        | none => simp [found] at run
        | some value =>
          simp [found] at run
          rcases run with ⟨rfl, rfl⟩
          have member : value ∈ fields := List.mem_of_getElem? found
          have valueReachable : globalsWithin (findValueGlobals value) reachable := by
            intro key keyFound
            apply firstReachable key
            simpa only [findValueGlobals] using findValuesGlobals_member fields value member key keyFound
          have valueSafe : valueHasEval value = false := by
            have allSafe : valuesNoEval fields := (valuesHaveEval_eq_false_iff fields).mp
              (by simpa [valueHasEval] using firstSafe)
            exact allSafe value member
          refine ⟨target, related, ?_, (primitiveResult_value_invariants reachable value valueReachable valueSafe).1,
            (primitiveResult_value_invariants reachable value valueReachable valueSafe).2⟩
          simp [FlatSem.doApp, FlatSem.doAppFlat, found]
      case loc flag address =>
        by_cases zero : index = 0
        · simp [zero] at run
          cases lookup : storeLookup address source.refs with
          | none => simp [lookup] at run
          | some ref =>
            cases ref <;> simp [lookup] at run
            case refv value =>
              rcases run with ⟨rfl, rfl⟩
              have member : StoreValue.refv value ∈ source.refs :=
                List.mem_of_getElem? (by simpa [storeLookup] using lookup)
              have valueReachable : globalsWithin (findValueGlobals value) reachable := by
                exact (findRefsGlobals_within_iff _ _).mp related.2.2.2.2.1 (.refv value) member
              have valueSafe : valueHasEval value = false := related.2.2.2.2.2 (.refv value) member
              refine ⟨target, related, ?_, (primitiveResult_value_invariants reachable value valueReachable valueSafe).1,
                (primitiveResult_value_invariants reachable value valueReachable valueSafe).2⟩
              simp [FlatSem.doApp, FlatSem.doAppFlat, zero, ← related.2.1, lookup]
        · simp [zero] at run

/-- The flat identity operation preserves the primitive simulation invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_id {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.id ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra .id [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source .id values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target .id values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | cons value rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      have valueReachable : globalsWithin (findValueGlobals value) reachable :=
        ((globalsWithin_union _ _ _).mp (by simpa [findValuesGlobals] using valuesReachable)).1
      have valueSafe : valueHasEval value = false := valuesSafe value (by simp)
      simp [FlatSem.doApp, FlatSem.doAppFlat] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨target, related, ?_, (primitiveResult_value_invariants reachable value valueReachable valueSafe).1,
        (primitiveResult_value_invariants reachable value valueReachable valueSafe).2⟩
      simp [FlatSem.doApp, FlatSem.doAppFlat]

/-- The flat constructor-length test preserves the simulation invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_lenEq {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (length : Nat)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.lenEq length ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.lenEq length) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.lenEq length) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.lenEq length) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | cons first rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      cases first <;> simp [FlatSem.doApp, FlatSem.doAppFlat] at run
      case conv stamp fields =>
        rcases run with ⟨rfl, rfl⟩
        have resultSafe := primitiveResult_value_invariants reachable (FlatSem.boolValue (fields.length == length))
          (by simp [FlatSem.boolValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
          (by simp [FlatSem.boolValue, valueHasEval, valuesHaveEval])
        exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppFlat], resultSafe.1, resultSafe.2⟩

/-- The flat constructor-tag and length test preserves the simulation invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_tagLenEq {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (tag length : Nat)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.tagLenEq tag length ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.tagLenEq tag length) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.tagLenEq tag length) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.tagLenEq tag length) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | cons first rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      cases first <;> simp [FlatSem.doApp, FlatSem.doAppFlat] at run
      case conv stamp fields =>
        cases stamp with
        | none => simp at run
        | some pair =>
          obtain ⟨actual, typ⟩ := pair
          simp at run
          rcases run with ⟨rfl, rfl⟩
          have resultSafe := primitiveResult_value_invariants reachable
            (FlatSem.boolValue (actual == tag && fields.length == length))
            (by simp [FlatSem.boolValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
            (by simp [FlatSem.boolValue, valueHasEval, valuesHaveEval])
          exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppFlat], resultSafe.1, resultSafe.2⟩

end Flapjack.Compiler.Backend.FlatElim
