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

end Flapjack.Compiler.Backend.FlatElim
