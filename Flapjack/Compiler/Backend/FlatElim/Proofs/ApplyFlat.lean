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

/-- A reachable global lookup is preserved by elimination, and the returned
value satisfies the original primitive-result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_globalLookup {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (index : Nat)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.globalVarLookup index ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (opReachable : globalsWithin (findLookups (.app tra (.globalVarLookup index) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.globalVarLookup index) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.globalVarLookup index) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | cons first rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | nil =>
    have reachableIndex : sptMem index reachable := by
      apply opReachable index
      simp only [findLookups, findGlobals, destGlobalVarLookup, findGlobalsList]
      exact (sptMem_sptInsert index index () .ln).mpr (Or.inl rfl)
    cases lookup : source.globals[index]? with
    | none => simp [FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
    | some entry =>
      cases entry with
      | none => simp [FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
      | some value =>
        simp [FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
        rcases run with ⟨rfl, rfl⟩
        have globals := related.2.2.2.1
        have sourceBound : index < source.globals.length := (List.getElem?_eq_some_iff.mp lookup).choose
        have targetBound : index < target.globals.length := by simpa [← globals.1] using sourceBound
        have same := globals.2.1 index reachableIndex targetBound
        have targetLookup : target.globals[index]? = some (some value) := by
          cases targetEntry : target.globals[index]? with
          | none =>
            have tooLarge := List.getElem?_eq_none_iff.mp targetEntry
            omega
          | some entry =>
            simp [lookup, targetEntry] at same
            simpa [targetEntry] using same.symm
        have closed := globals.2.2.2.2 index value reachableIndex targetBound (by simp [targetLookup])
        have resultSafe := primitiveResult_value_invariants reachable value closed.2 closed.1
        exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppFlat, targetLookup],
          resultSafe.1, resultSafe.2⟩

/-- Initializing an empty global slot preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_globalInit {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (index : Nat)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.globalVarInit index ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.globalVarInit index) [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.globalVarInit index) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.globalVarInit index) values = some (targetNext, result) ∧
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
      cases lookup : source.globals[index]? with
      | none => simp [FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
      | some entry =>
        cases entry with
        | some old => simp [FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
        | none =>
          simp [FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
          rcases run with ⟨rfl, rfl⟩
          have globals := related.2.2.2.1
          have sourceBound : index < source.globals.length := (List.getElem?_eq_some_iff.mp lookup).choose
          have targetBound : index < target.globals.length := by simpa [← globals.1] using sourceBound
          have targetD := globals.2.2.2.1 index targetBound (by simp [lookup])
          have targetEmpty : target.globals[index]? = some none := by
            cases targetEntry : target.globals[index]? with
            | none =>
              have tooLarge := List.getElem?_eq_none_iff.mp targetEntry
              omega
            | some entry =>
              simp [targetEntry] at targetD
              simpa [targetEntry] using targetD
          have newGlobals := globalsRel_set_init reachable source.globals target.globals index value
            globals lookup targetEmpty valueSafe valueReachable
          have resultSafe := primitiveResult_value_invariants reachable FlatSem.unitValue
            (by simp [FlatSem.unitValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
            (by simp [FlatSem.unitValue, valueHasEval, valuesHaveEval])
          refine ⟨{ target with globals := target.globals.set index (some value) }, ?_, ?_, resultSafe.1, resultSafe.2⟩
          · exact ⟨related.1, related.2.1, related.2.2.1, newGlobals, related.2.2.2.2⟩
          · simp [FlatSem.doApp, FlatSem.doAppFlat, targetEmpty]

/-- Global-slot allocation preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_globalAlloc {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (count : Nat)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.globalVarAlloc count ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.globalVarAlloc count) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.globalVarAlloc count) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.globalVarAlloc count) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | cons first rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | nil =>
    simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    rcases run with ⟨rfl, rfl⟩
    have resultSafe := primitiveResult_value_invariants reachable FlatSem.unitValue
      (by simp [FlatSem.unitValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
      (by simp [FlatSem.unitValue, valueHasEval, valuesHaveEval])
    refine ⟨{ target with globals := target.globals ++ List.replicate count none }, ?_, ?_,
      resultSafe.1, resultSafe.2⟩
    · exact ⟨related.1, related.2.1, related.2.2.1,
        globalsRel_append_empty reachable source.globals target.globals count related.2.2.2.1,
        related.2.2.2.2⟩
    · simp [FlatSem.doApp, FlatSem.doAppFlat]

/-- All flat-specific primitive operations satisfy the original simulation.
The source-operation cases are handled separately. -/
theorem doApp_some_flatStateRel_nonSource {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (op : FlatLang.Op)
    (result : Result FlatSem.Value FlatSem.Value) (unusedRemovedState : G) (tra : BackendCommon.Tra)
    (notSource : ∀ sourceOp, op ≠ .src sourceOp)
    (related : flatStateRel reachable source target)
    (opNotApply : op ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (opReachable : globalsWithin (findLookups (.app tra op [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source op values = some (next, result))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target op values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases op with
  | src sourceOp => exact (notSource sourceOp rfl).elim
  | globalVarAlloc count =>
    exact doApp_some_flatStateRel_globalAlloc reachable source target next values count result unusedRemovedState tra
      related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | globalVarInit index =>
    exact doApp_some_flatStateRel_globalInit reachable source target next values index result unusedRemovedState tra
      related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | globalVarLookup index =>
    exact doApp_some_flatStateRel_globalLookup reachable source target next values index result unusedRemovedState tra
      related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | tagLenEq tag length =>
    exact doApp_some_flatStateRel_tagLenEq reachable source target next values tag length result unusedRemovedState tra
      related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | lenEq length =>
    exact doApp_some_flatStateRel_lenEq reachable source target next values length result unusedRemovedState tra
      related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | el index =>
    exact doApp_some_flatStateRel_el reachable source target next values index result unusedRemovedState tra
      related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | id =>
    exact doApp_some_flatStateRel_id reachable source target next values result unusedRemovedState tra
      related opNotApply valuesReachable opReachable valuesSafe run notTypeError

end Flapjack.Compiler.Backend.FlatElim
