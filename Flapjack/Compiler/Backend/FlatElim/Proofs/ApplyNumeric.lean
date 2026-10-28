import Flapjack.Compiler.Backend.FlatElim.Proofs.ApplyCopy
import Flapjack.Compiler.Backend.FlatElim.Proofs.ApplyFlat

/-! Numeric and comparison primitive cases for the elimination simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- Every value produced by the flat numeric projection is a literal, a
Boolean, or an empty vector, so it is closed and cannot contain Eval. -/
theorem valueToFlat_invariants (reachable : NumSet) (value : SemanticPrimitivesHOL.Value) :
    globalsWithin (findValueGlobals (FlatSem.valueToFlat value)) reachable ∧
      valueHasEval (FlatSem.valueToFlat value) = false := by
  cases value <;> simp [FlatSem.valueToFlat, findValueGlobals, findValuesGlobals,
    valueHasEval, valuesHaveEval, globalsWithin, sptMem, sptDomain]
  case conv stamp values =>
    repeat' split
    all_goals simp_all [FlatSem.boolValue, findValueGlobals, findValuesGlobals, valueHasEval, valuesHaveEval]

/-- A closed, Eval-free raised value satisfies the primitive-result invariants. -/
theorem primitiveResult_raise_invariants (reachable : NumSet) (value : FlatSem.Value)
    (closed : globalsWithin (findValueGlobals value) reachable) (safe : valueHasEval value = false) :
    globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult (.err (.raise value)))) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult (.err (.raise value)))) := by
  constructor
  · simpa [findPrimitiveResultGlobals, findResultGlobals, Flapjack.EvaluateHOL.listResult] using closed
  · simpa [Flapjack.Compiler.Backend.FlatProps.resultValues, Flapjack.EvaluateHOL.listResult, valuesNoEval] using safe

/-- Numeric projection gives related results in related states when its
fixed exception value satisfies the result invariants. -/
theorem applyNumericProjection_related {C F : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (op : Flapjack.AstHOL.Op)
    (values : List FlatSem.Value) (errorValue : FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (related : flatStateRel reachable source target)
    (errorClosed : globalsWithin (findValueGlobals errorValue) reachable)
    (errorSafe : valueHasEval errorValue = false)
    (run : FlatSem.applyNumericProjection source op values errorValue = some (next, result)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.applyNumericProjection target op values errorValue = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  have ffiEq := related.2.2.1
  cases call : SemanticPrimitivesHOL.doApp ([], source.ffi) op (values.map FlatSem.flatToValue) with
  | none => simp [FlatSem.applyNumericProjection, call] at run
  | some pair =>
    obtain ⟨state, sourceResult⟩ := pair
    cases sourceResult with
    | val value =>
      simp [FlatSem.applyNumericProjection, call] at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨closed, safe⟩ := valueToFlat_invariants reachable value
      have resultSafe := primitiveResult_value_invariants reachable (FlatSem.valueToFlat value) closed safe
      exact ⟨target, related, by simp [FlatSem.applyNumericProjection, ← ffiEq, call], resultSafe.1, resultSafe.2⟩
    | err error =>
      cases error with
      | raise value =>
        simp [FlatSem.applyNumericProjection, call] at run
        rcases run with ⟨rfl, rfl⟩
        have resultSafe := primitiveResult_raise_invariants reachable errorValue errorClosed errorSafe
        exact ⟨target, related, by simp [FlatSem.applyNumericProjection, ← ffiEq, call], resultSafe.1, resultSafe.2⟩
      | abort error =>
        simp [FlatSem.applyNumericProjection, call] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, related, by simp [FlatSem.applyNumericProjection, ← ffiEq, call], ?_, ?_⟩
        · simp [findPrimitiveResultGlobals, findResultGlobals, Flapjack.EvaluateHOL.listResult,
            globalsWithin, sptMem, sptDomain]
        · simp [Flapjack.Compiler.Backend.FlatProps.resultValues, Flapjack.EvaluateHOL.listResult, valuesNoEval]

/-- The shift case preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_shift {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (width : Flapjack.AstHOL.WordSize) (shift : Flapjack.Shift) (amount : Nat)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src (.shift width shift amount) ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src (.shift width shift amount)) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src (.shift width shift amount)) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src (.shift width shift amount)) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  obtain ⟨targetNext, stateRel, evaluated, closed, safe⟩ :=
    applyNumericProjection_related reachable source target next (.shift width shift amount) values FlatSem.divExnV result related
      (by simp [FlatSem.divExnV, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
      (by simp [FlatSem.divExnV, valueHasEval, valuesHaveEval])
      (by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using run)
  exact ⟨targetNext, stateRel, by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using evaluated, closed, safe⟩

/-- The arith case preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_arith {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (action : Flapjack.AstHOL.Arith) (typ : Flapjack.AstHOL.PrimType)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src (.arith action typ) ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src (.arith action typ)) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src (.arith action typ)) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src (.arith action typ)) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  obtain ⟨targetNext, stateRel, evaluated, closed, safe⟩ :=
    applyNumericProjection_related reachable source target next (.arith action typ) values FlatSem.divExnV result related
      (by simp [FlatSem.divExnV, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
      (by simp [FlatSem.divExnV, valueHasEval, valuesHaveEval])
      (by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using run)
  exact ⟨targetNext, stateRel, by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using evaluated, closed, safe⟩

/-- The fromTo case preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_fromTo {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (fromType toType : Flapjack.AstHOL.PrimType)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src (.fromTo fromType toType) ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src (.fromTo fromType toType)) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src (.fromTo fromType toType)) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src (.fromTo fromType toType)) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  obtain ⟨targetNext, stateRel, evaluated, closed, safe⟩ :=
    applyNumericProjection_related reachable source target next (.fromTo fromType toType) values FlatSem.chrExnV result related
      (by simp [FlatSem.chrExnV, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
      (by simp [FlatSem.chrExnV, valueHasEval, valuesHaveEval])
      (by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using run)
  exact ⟨targetNext, stateRel, by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using evaluated, closed, safe⟩

/-- The equality case preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_equality {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) 
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .equality ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .equality) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .equality) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .equality) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
    | cons second rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
      | nil =>
        cases comparison : FlatSem.doEq first second with
        | typeError => simp [FlatSem.doApp, FlatSem.doAppNumeric, comparison] at run
        | val value =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, comparison] at run
          rcases run with ⟨rfl, rfl⟩
          have resultSafe := primitiveResult_value_invariants reachable (FlatSem.boolValue value)
            (by simp [FlatSem.boolValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
            (by simp [FlatSem.boolValue, valueHasEval, valuesHaveEval])
          exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppNumeric, comparison], resultSafe.1, resultSafe.2⟩

/-- The test case preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_test {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value) (test : Flapjack.AstHOL.Test) (typ : Flapjack.AstHOL.PrimType)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src (.test test typ) ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src (.test test typ)) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src (.test test typ)) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src (.test test typ)) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
    | cons second rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
      | nil =>
        cases comparison : FlatSem.doTest test typ first second with
        | typeError => simp [FlatSem.doApp, FlatSem.doAppNumeric, comparison] at run
        | val value =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, comparison] at run
          rcases run with ⟨rfl, rfl⟩
          have resultSafe := primitiveResult_value_invariants reachable (FlatSem.boolValue value)
            (by simp [FlatSem.boolValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
            (by simp [FlatSem.boolValue, valueHasEval, valuesHaveEval])
          exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppNumeric, comparison], resultSafe.1, resultSafe.2⟩

/-- Primitive application preserves the flat-elimination state relation and
result invariants. The underlying assembled evaluator still requires its full
source and carrier review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel {C F G : Type} (reachable : NumSet)
    (source target : FlatSem.State C F) (op : FlatLang.Op) (values : List FlatSem.Value)
    (next : FlatSem.State C F) (result : Result FlatSem.Value FlatSem.Value)
    (unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target) (opNotApply : op ≠ .src .opapp)
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
  | src sourceOp =>
    cases sourceOp with
    | arith action typ =>
      exact doApp_some_flatStateRel_arith reachable source target next values action typ result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | fromTo fromType toType =>
      exact doApp_some_flatStateRel_fromTo reachable source target next values fromType toType result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | shift width shift amount =>
      exact doApp_some_flatStateRel_shift reachable source target next values width shift amount result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | equality  =>
      exact doApp_some_flatStateRel_equality reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | test test typ =>
      exact doApp_some_flatStateRel_test reachable source target next values test typ result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | opassign  =>
      exact doApp_some_flatStateRel_assign reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | opref  =>
      exact doApp_some_flatStateRel_ref reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aw8alloc  =>
      exact doApp_some_flatStateRel_byteArray reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aw8sub  =>
      exact doApp_some_flatStateRel_byteArraySub reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aw8length  =>
      exact doApp_some_flatStateRel_byteArrayLength reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aw8update  =>
      exact doApp_some_flatStateRel_byteArrayUpdate reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | copyStrStr  =>
      exact doApp_some_flatStateRel_copyStrStr reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | copyStrAw8  =>
      exact doApp_some_flatStateRel_copyStrAw8 reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | copyAw8Str  =>
      exact doApp_some_flatStateRel_copyAw8Str reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | copyAw8Aw8  =>
      exact doApp_some_flatStateRel_copyAw8Aw8 reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | xorAw8StrUnsafe  =>
      exact doApp_some_flatStateRel_xorAw8StrUnsafe reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | implode  =>
      exact doApp_some_flatStateRel_stringImplode reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | explode  =>
      exact doApp_some_flatStateRel_stringExplode reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | strsub  =>
      exact doApp_some_flatStateRel_stringSub reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | strlen  =>
      exact doApp_some_flatStateRel_stringLength reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | strcat  =>
      exact doApp_some_flatStateRel_stringConcat reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | vfromList  =>
      exact doApp_some_flatStateRel_vectorFromList reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | vsub  =>
      exact doApp_some_flatStateRel_vectorSub reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | vlength  =>
      exact doApp_some_flatStateRel_vectorLength reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aalloc  =>
      exact doApp_some_flatStateRel_array reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aallocFixed  =>
      exact doApp_some_flatStateRel_fixedArray reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | asub  =>
      exact doApp_some_flatStateRel_arraySub reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | alength  =>
      exact doApp_some_flatStateRel_arrayLength reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aupdate  =>
      exact doApp_some_flatStateRel_arrayUpdate reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | vsubUnsafe  =>
      exact doApp_some_flatStateRel_vectorSubUnsafe reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | asubUnsafe  =>
      exact doApp_some_flatStateRel_arraySubUnsafe reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aupdateUnsafe  =>
      exact doApp_some_flatStateRel_arrayUpdateUnsafe reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aw8subUnsafe  =>
      exact doApp_some_flatStateRel_byteArraySubUnsafe reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | aw8updateUnsafe  =>
      exact doApp_some_flatStateRel_byteArrayUpdateUnsafe reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | listAppend  =>
      exact doApp_some_flatStateRel_listAppend reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | configGC  =>
      exact doApp_some_flatStateRel_configGC reachable source target next values  result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | ffi name =>
      exact doApp_some_flatStateRel_ffi reachable source target next values name result unusedRemovedState tra
        related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | thunkOp thunk =>
      cases thunk with
      | allocThunk mode =>
        exact doApp_some_flatStateRel_thunkAlloc reachable source target next values mode result unusedRemovedState tra
          related opNotApply valuesReachable opReachable valuesSafe run notTypeError
      | forceThunk =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | updateThunk mode =>
        exact doApp_some_flatStateRel_thunkUpdate reachable source target next values mode result unusedRemovedState tra
          related opNotApply valuesReachable opReachable valuesSafe run notTypeError
    | opapp => exact (opNotApply rfl).elim
    | opderef | aallocEmpty | eval | envId =>
      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | globalVarAlloc count =>
    exact doApp_some_flatStateRel_nonSource reachable source target next values (.globalVarAlloc count) result unusedRemovedState tra
      (by intro sourceOp h; cases h) related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | globalVarInit index =>
    exact doApp_some_flatStateRel_nonSource reachable source target next values (.globalVarInit index) result unusedRemovedState tra
      (by intro sourceOp h; cases h) related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | globalVarLookup index =>
    exact doApp_some_flatStateRel_nonSource reachable source target next values (.globalVarLookup index) result unusedRemovedState tra
      (by intro sourceOp h; cases h) related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | tagLenEq tag length =>
    exact doApp_some_flatStateRel_nonSource reachable source target next values (.tagLenEq tag length) result unusedRemovedState tra
      (by intro sourceOp h; cases h) related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | lenEq length =>
    exact doApp_some_flatStateRel_nonSource reachable source target next values (.lenEq length) result unusedRemovedState tra
      (by intro sourceOp h; cases h) related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | el index =>
    exact doApp_some_flatStateRel_nonSource reachable source target next values (.el index) result unusedRemovedState tra
      (by intro sourceOp h; cases h) related opNotApply valuesReachable opReachable valuesSafe run notTypeError
  | id  =>
    exact doApp_some_flatStateRel_nonSource reachable source target next values (.id) result unusedRemovedState tra
      (by intro sourceOp h; cases h) related opNotApply valuesReachable opReachable valuesSafe run notTypeError

end Flapjack.Compiler.Backend.FlatElim
