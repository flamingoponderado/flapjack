import Flapjack.Compiler.Backend.FlatElim.Proofs.ApplyMemory

/-! Data primitive cases for the flat-elimination simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- The vectorSub case preserves related states and primitive-result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_vectorSub {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .vsub ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .vsub) [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .vsub) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .vsub) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | cons second rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        have firstReachable : globalsWithin (findValueGlobals first) reachable :=
          (findValuesGlobals_within_iff _ _).mp valuesReachable first (by simp)
        have firstSafe : valueHasEval first = false := valuesSafe first (by simp)
        cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
        case vectorv items =>
          cases second <;> try simp at run
          case litv lit =>
            cases lit <;> try simp at run
            case intLit index =>
              have itemsReachable : globalsWithin (findValuesGlobals items) reachable := by
                simpa [findValueGlobals] using firstReachable
              have itemsSafe : valuesNoEval items := (valuesHaveEval_eq_false_iff items).mp
                (by simpa [valueHasEval] using firstSafe)
              have opEq : (Flapjack.AstHOL.Op.vsub == .vsubUnsafe) = false := by decide
              obtain ⟨targetNext, stateRel, read, closed, safe⟩ :=
                readIndexed_array_related reachable source target next false items index result related
                  itemsReachable itemsSafe (by simpa [opEq] using run)
              refine ⟨targetNext, stateRel, ?_, closed, safe⟩
              simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, opEq] using read

/-- The vectorSubUnsafe case preserves related states and primitive-result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_vectorSubUnsafe {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .vsubUnsafe ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .vsubUnsafe) [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .vsubUnsafe) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .vsubUnsafe) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | cons second rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        have firstReachable : globalsWithin (findValueGlobals first) reachable :=
          (findValuesGlobals_within_iff _ _).mp valuesReachable first (by simp)
        have firstSafe : valueHasEval first = false := valuesSafe first (by simp)
        cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
        case vectorv items =>
          cases second <;> try simp at run
          case litv lit =>
            cases lit <;> try simp at run
            case intLit index =>
              have itemsReachable : globalsWithin (findValuesGlobals items) reachable := by
                simpa [findValueGlobals] using firstReachable
              have itemsSafe : valuesNoEval items := (valuesHaveEval_eq_false_iff items).mp
                (by simpa [valueHasEval] using firstSafe)

              obtain ⟨targetNext, stateRel, read, closed, safe⟩ :=
                readIndexed_array_related reachable source target next true items index result related
                  itemsReachable itemsSafe (by simpa  using run)
              refine ⟨targetNext, stateRel, ?_, closed, safe⟩
              simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] using read

/-- The vectorLength case preserves related states and primitive-result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_vectorLength {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .vlength ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .vlength) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .vlength) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .vlength) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons first rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      case vectorv items =>
        rcases run with ⟨rfl, rfl⟩
        have resultSafe := primitiveResult_value_invariants reachable (FlatSem.Value.litv (.intLit items.length))
          (by simp [findValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [valueHasEval])
        exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData],
          resultSafe.1, resultSafe.2⟩

/-- The stringLength case preserves related states and primitive-result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_stringLength {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .strlen ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .strlen) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .strlen) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .strlen) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons first rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      case litv lit =>
        cases lit <;> try simp at run
        case strLit str =>
          rcases run with ⟨rfl, rfl⟩
          have resultSafe := primitiveResult_value_invariants reachable (FlatSem.Value.litv (.intLit str.explode.length))
            (by simp [findValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [valueHasEval])
          exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData],
            resultSafe.1, resultSafe.2⟩

/-- String subscripting preserves related states and result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_stringSub {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .strsub ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .strsub) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .strsub) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .strsub) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | cons second rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
        case litv lit =>
          cases lit <;> try simp at run
          case strLit str =>
            cases second <;> try simp at run
            case litv lit =>
              cases lit <;> try simp at run
              case intLit index =>
                obtain ⟨targetNext, stateRel, read, closed, safe⟩ :=
                  readIndexed_literal_related reachable source target next false str.explode index
                    Flapjack.AstHOL.Lit.char result related (by simpa using run)
                refine ⟨targetNext, stateRel, ?_, closed, safe⟩
                simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] using read

/-- The stringImplode case preserves related states and primitive-result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_stringImplode {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .implode ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .implode) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .implode) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .implode) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons value rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases charsEq : FlatSem.valueToCharList value with
      | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, charsEq] at run
      | some chars =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, charsEq] at run
        rcases run with ⟨rfl, rfl⟩
        have resultSafe := primitiveResult_value_invariants reachable (FlatSem.Value.litv (.strLit (.implode chars)))
          (by simp [findValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [valueHasEval])
        exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, charsEq],
          resultSafe.1, resultSafe.2⟩

/-- The stringConcat case preserves related states and primitive-result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_stringConcat {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .strcat ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .strcat) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .strcat) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .strcat) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons value rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases partsEq : FlatSem.valueToList value with
      | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, partsEq] at run
      | some parts =>
        cases joinedEq : FlatSem.valuesToString parts with
        | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, partsEq, joinedEq] at run
        | some text =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, partsEq, joinedEq] at run
          rcases run with ⟨rfl, rfl⟩
          have resultSafe := primitiveResult_value_invariants reachable (FlatSem.Value.litv (.strLit text))
            (by simp [findValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [valueHasEval])
          exact ⟨target, related,
            by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, partsEq, joinedEq],
            resultSafe.1, resultSafe.2⟩

/-- Encoding a list preserves its reachability and Eval-free invariants. -/
theorem listToValue_invariants (values : List FlatSem.Value) (reachable : NumSet)
    (closed : globalsWithin (findValuesGlobals values) reachable) (safe : valuesNoEval values) :
    globalsWithin (findValueGlobals (FlatSem.listToValue values)) reachable ∧
      valueHasEval (FlatSem.listToValue values) = false := by
  induction values with
  | nil =>
    constructor
    · simp [FlatSem.listToValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain]
    · simp [FlatSem.listToValue, valueHasEval, valuesHaveEval]
  | cons value rest ih =>
    have parts := (globalsWithin_union _ _ _).mp (by simpa [findValuesGlobals] using closed)
    have headSafe : valueHasEval value = false := safe value (by simp)
    have tailSafe : valuesNoEval rest := by
      intro item member
      exact safe item (by simp [member])
    obtain ⟨tailClosed, tailNoEval⟩ := ih parts.2 tailSafe
    constructor
    · simp only [FlatSem.listToValue, findValueGlobals, findValuesGlobals, globalsWithin_union]
      exact ⟨parts.1, tailClosed, by simp [globalsWithin, sptMem, sptDomain]⟩
    · simp [FlatSem.listToValue, valueHasEval, valuesHaveEval, headSafe, tailNoEval]

/-- Decoding a flat list preserves reachability and the absence of Eval. -/
theorem valueToList_invariants (value : FlatSem.Value) (values : List FlatSem.Value)
    (reachable : NumSet) (decoded : FlatSem.valueToList value = some values)
    (closed : globalsWithin (findValueGlobals value) reachable) (safe : valueHasEval value = false) :
    globalsWithin (findValuesGlobals values) reachable ∧ valuesNoEval values := by
  induction value using FlatSem.valueToList.induct generalizing values with
  | case1 cid tid valid =>
    simp [FlatSem.valueToList, valid] at decoded
    subst values
    constructor
    · simp [findValuesGlobals, globalsWithin, sptMem, sptDomain]
    · simp [valuesNoEval]
  | case2 cid tid invalid => simp [FlatSem.valueToList, invalid] at decoded
  | case3 cid tid head tail valid ih =>
    cases tailDecoded : FlatSem.valueToList tail with
    | none => simp [FlatSem.valueToList, valid, tailDecoded] at decoded
    | some rest =>
      simp [FlatSem.valueToList, valid, tailDecoded] at decoded
      subst values
      have parts : globalsWithin (findValueGlobals head) reachable ∧
          globalsWithin (findValueGlobals tail) reachable := by
        simp only [findValueGlobals, findValuesGlobals, globalsWithin_union] at closed
        exact ⟨closed.1, closed.2.1⟩
      have safeParts : valueHasEval head = false ∧ valueHasEval tail = false := by
        simpa [valueHasEval, valuesHaveEval] using safe
      obtain ⟨restClosed, restSafe⟩ := ih rest tailDecoded parts.2 safeParts.2
      constructor
      · simpa [findValuesGlobals, globalsWithin_union] using And.intro parts.1 restClosed
      · simpa [valuesNoEval] using And.intro safeParts.1 restSafe
  | case4 cid tid head tail invalid => simp [FlatSem.valueToList, invalid] at decoded
  | case5 value noNil noCons =>
    simp only [FlatSem.valueToList] at decoded
    simp at decoded

/-- Decoding a list cannot add global dependencies. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_v_to_list"]
theorem findValueGlobals_valueToList (value : FlatSem.Value) (reachable : NumSet)
    (values : List FlatSem.Value) (closed : globalsWithin (findValueGlobals value) reachable)
    (decoded : FlatSem.valueToList value = some values) :
    globalsWithin (findValuesGlobals values) reachable := by
  induction value using FlatSem.valueToList.induct generalizing values with
  | case1 cid tid valid =>
    simp [FlatSem.valueToList, valid] at decoded
    subst values
    simp [findValuesGlobals, globalsWithin, sptMem, sptDomain]
  | case2 cid tid invalid => simp [FlatSem.valueToList, invalid] at decoded
  | case3 cid tid head tail valid ih =>
    cases tailDecoded : FlatSem.valueToList tail with
    | none => simp [FlatSem.valueToList, valid, tailDecoded] at decoded
    | some rest =>
      simp [FlatSem.valueToList, valid, tailDecoded] at decoded
      subst values
      simp only [findValueGlobals, findValuesGlobals, globalsWithin_union] at closed
      simpa only [findValuesGlobals] using
        (globalsWithin_union _ _ _).mpr ⟨closed.1, ih rest closed.2.1 tailDecoded⟩
  | case4 cid tid head tail invalid => simp [FlatSem.valueToList, invalid] at decoded
  | case5 value noNil noCons =>
    simp only [FlatSem.valueToList] at decoded
    simp at decoded

/-- Encoding a list cannot add global dependencies. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_list_to_v"]
theorem findValueGlobals_listToValue (values : List FlatSem.Value) (reachable : NumSet)
    (value : FlatSem.Value) (closed : globalsWithin (findValuesGlobals values) reachable)
    (encoded : FlatSem.listToValue values = value) :
    globalsWithin (findValueGlobals value) reachable := by
  subst value
  induction values with
  | nil => simp [FlatSem.listToValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain]
  | cons value rest ih =>
    have parts := (globalsWithin_union _ _ _).mp (by simpa [findValuesGlobals] using closed)
    simp only [FlatSem.listToValue, findValueGlobals, findValuesGlobals, globalsWithin_union]
    exact ⟨parts.1, ih parts.2, by simp [globalsWithin, sptMem, sptDomain]⟩

/-- Encoding an append preserves the combined global-dependency bound. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_list_to_v_APPEND"]
theorem findValueGlobals_listToValue_append (left : List FlatSem.Value) (reachable : NumSet)
    (right : List FlatSem.Value) (leftClosed : globalsWithin (findValuesGlobals left) reachable)
    (rightClosed : globalsWithin (findValuesGlobals right) reachable) :
    globalsWithin (findValueGlobals (FlatSem.listToValue (left ++ right))) reachable := by
  apply findValueGlobals_listToValue (left ++ right) reachable _ ?_ rfl
  apply (findValuesGlobals_within_iff _ _).mpr
  intro value member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact (findValuesGlobals_within_iff _ _).mp leftClosed value leftMember
  · exact (findValuesGlobals_within_iff _ _).mp rightClosed value rightMember

/-- Encoding a value list preserves its dynamic-Eval test. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "v_has_Eval_list_to_v"]
theorem valueHasEval_listToValue (values : List FlatSem.Value) :
    valueHasEval (FlatSem.listToValue values) = valuesHaveEval values := by
  induction values with
  | nil => simp [FlatSem.listToValue, valueHasEval, valuesHaveEval]
  | cons value rest ih =>
    simp [FlatSem.listToValue, valueHasEval, valuesHaveEval, ih]

/-- Successful list decoding preserves the dynamic-Eval test. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "v_has_Eval_v_to_list"]
theorem valueHasEval_valueToList (value : FlatSem.Value) (values : List FlatSem.Value)
    (decoded : FlatSem.valueToList value = some values) :
    valueHasEval value = valuesHaveEval values := by
  induction value using FlatSem.valueToList.induct generalizing values with
  | case1 cid tid valid =>
    simp [FlatSem.valueToList, valid] at decoded
    subst values
    simp [valueHasEval, valuesHaveEval]
  | case2 cid tid invalid => simp [FlatSem.valueToList, invalid] at decoded
  | case3 cid tid head tail valid ih =>
    cases tailDecoded : FlatSem.valueToList tail with
    | none => simp [FlatSem.valueToList, valid, tailDecoded] at decoded
    | some rest =>
      simp [FlatSem.valueToList, valid, tailDecoded] at decoded
      subst values
      simp [valueHasEval, valuesHaveEval, ih rest tailDecoded]
  | case4 cid tid head tail invalid => simp [FlatSem.valueToList, invalid] at decoded
  | case5 value noNil noCons =>
    simp only [FlatSem.valueToList] at decoded
    simp at decoded

/-- String explosion preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_stringExplode {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .explode ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .explode) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .explode) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .explode) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons first rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      case litv lit =>
        cases lit <;> try simp at run
        case strLit str =>
          rcases run with ⟨rfl, rfl⟩
          let chars := str.explode.map (FlatSem.Value.litv ∘ Flapjack.AstHOL.Lit.char)
          have charsClosed : globalsWithin (findValuesGlobals chars) reachable := by
            apply (findValuesGlobals_within_iff _ _).mpr
            intro value member
            obtain ⟨char, _, rfl⟩ := List.mem_map.mp member
            simp [findValueGlobals, globalsWithin, sptMem, sptDomain]
          have charsSafe : valuesNoEval chars := by
            intro value member
            obtain ⟨char, _, rfl⟩ := List.mem_map.mp member
            simp [valueHasEval]
          obtain ⟨valueClosed, valueSafe⟩ := listToValue_invariants chars reachable charsClosed charsSafe
          have resultSafe := primitiveResult_value_invariants reachable (FlatSem.listToValue chars) valueClosed valueSafe
          exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData],
            resultSafe.1, resultSafe.2⟩

/-- Garbage-collector configuration preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_configGC {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .configGC ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .configGC) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .configGC) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .configGC) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | cons second rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
        case litv lit =>
          cases lit <;> try simp at run
          case intLit firstNum =>
            cases second <;> try simp at run
            case litv lit =>
              cases lit <;> try simp at run
              case intLit secondNum =>
                rcases run with ⟨rfl, rfl⟩
                have resultSafe := primitiveResult_value_invariants reachable FlatSem.unitValue
                  (by simp [FlatSem.unitValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
                  (by simp [FlatSem.unitValue, valueHasEval, valuesHaveEval])
                exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData],
                  resultSafe.1, resultSafe.2⟩

/-- Converting a list to a vector preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_vectorFromList {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .vfromList ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .vfromList) [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .vfromList) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .vfromList) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons value rest =>
    cases rest with
    | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      have valueClosed : globalsWithin (findValueGlobals value) reachable :=
        (findValuesGlobals_within_iff _ _).mp valuesReachable value (by simp)
      have valueSafe : valueHasEval value = false := valuesSafe value (by simp)
      cases decoded : FlatSem.valueToList value with
      | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded] at run
      | some items =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨itemsClosed, itemsSafe⟩ := valueToList_invariants value items reachable decoded valueClosed valueSafe
        have vectorClosed : globalsWithin (findValueGlobals (.vectorv items)) reachable := by
          simpa [findValueGlobals] using itemsClosed
        have vectorSafe : valueHasEval (.vectorv items) = false := by
          simpa [valueHasEval] using (valuesHaveEval_eq_false_iff items).mpr itemsSafe
        have resultSafe := primitiveResult_value_invariants reachable (.vectorv items) vectorClosed vectorSafe
        exact ⟨target, related, by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded],
          resultSafe.1, resultSafe.2⟩

/-- Appending decoded lists preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_listAppend {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .listAppend ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .listAppend) [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .listAppend) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .listAppend) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | cons left rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | cons right rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        have leftClosed : globalsWithin (findValueGlobals left) reachable :=
          (findValuesGlobals_within_iff _ _).mp valuesReachable left (by simp)
        have rightClosed : globalsWithin (findValueGlobals right) reachable :=
          (findValuesGlobals_within_iff _ _).mp valuesReachable right (by simp)
        have leftSafe : valueHasEval left = false := valuesSafe left (by simp)
        have rightSafe : valueHasEval right = false := valuesSafe right (by simp)
        cases leftDecoded : FlatSem.valueToList left with
        | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, leftDecoded] at run
        | some leftItems =>
          cases rightDecoded : FlatSem.valueToList right with
          | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, leftDecoded, rightDecoded] at run
          | some rightItems =>
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, leftDecoded, rightDecoded] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨leftItemsClosed, leftItemsSafe⟩ := valueToList_invariants left leftItems reachable leftDecoded leftClosed leftSafe
            obtain ⟨rightItemsClosed, rightItemsSafe⟩ := valueToList_invariants right rightItems reachable rightDecoded rightClosed rightSafe
            have combinedClosed : globalsWithin (findValuesGlobals (leftItems ++ rightItems)) reachable := by
              apply (findValuesGlobals_within_iff _ _).mpr
              intro value member
              rcases List.mem_append.mp member with leftMember | rightMember
              · exact (findValuesGlobals_within_iff _ _).mp leftItemsClosed value leftMember
              · exact (findValuesGlobals_within_iff _ _).mp rightItemsClosed value rightMember
            have combinedSafe : valuesNoEval (leftItems ++ rightItems) := by
              intro value member
              rcases List.mem_append.mp member with leftMember | rightMember
              · exact leftItemsSafe value leftMember
              · exact rightItemsSafe value rightMember
            obtain ⟨resultClosed, resultNoEval⟩ := listToValue_invariants (leftItems ++ rightItems) reachable combinedClosed combinedSafe
            have resultSafe := primitiveResult_value_invariants reachable (FlatSem.listToValue (leftItems ++ rightItems)) resultClosed resultNoEval
            exact ⟨target, related,
              by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, leftDecoded, rightDecoded],
              resultSafe.1, resultSafe.2⟩

end Flapjack.Compiler.Backend.FlatElim
