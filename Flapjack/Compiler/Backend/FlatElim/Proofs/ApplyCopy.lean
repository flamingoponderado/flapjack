import Flapjack.Compiler.Backend.FlatElim.Proofs.ApplyData

/-! String and byte-array copy cases for the flat-elimination simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- Replacing an existing byte array by arbitrary bytes preserves related
states; bytes carry no global or Eval dependencies. -/
theorem byteStoreUpdate_related {C F : Type} (reachable : NumSet)
    (source target : FlatSem.State C F) (address : Nat) (old new : List (BitVec 8))
    (related : flatStateRel reachable source target) (lookup : storeLookup address source.refs = some (.w8array old)) :
    storeAssign address (.w8array new) source.refs = some (source.refs.set address (.w8array new)) ∧
    storeAssign address (.w8array new) target.refs = some (target.refs.set address (.w8array new)) ∧
    flatStateRel reachable { source with refs := source.refs.set address (.w8array new) }
      { target with refs := target.refs.set address (.w8array new) } := by
  have lookup' : source.refs[address]? = some (.w8array old) := by simpa [storeLookup] using lookup
  have assigned : storeAssign address (.w8array new) source.refs = some (source.refs.set address (.w8array new)) := by
    simp [storeAssign, lookup', storeValueSameType]
  refine ⟨assigned, ?_, ?_⟩
  · simpa [← related.2.1] using assigned
  · exact flatStateRel_setRefs reachable source target address (.w8array new) related
      (by simp [storeValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [storeHasNoEval])

/-- Copying a substring preserves related states and result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_copyStrStr {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .copyStrStr ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .copyStrStr) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .copyStrStr) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .copyStrStr) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
    | cons second rest =>
      cases rest with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
      | cons third rest =>
        cases rest with
        | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
        | nil =>
          cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
          case litv lit =>
            cases lit <;> try simp at run
            case strLit str =>
              cases second <;> try simp at run
              case litv lit =>
                cases lit <;> try simp at run
                case intLit offset =>
                  cases third <;> try simp at run
                  case litv lit =>
                    cases lit <;> try simp at run
                    case intLit length =>
                      cases copied : copyArray (str.explode, offset) length none with
                      | none =>
                        simp [copied] at run
                        obtain ⟨targetNext, stateRel, failed, closed, safe⟩ :=
                          boundsFailure_related reachable source target next false result related run
                        exact ⟨targetNext, stateRel,
                          by simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
                            FlatSem.doAppCopy, copied] using failed, closed, safe⟩
                      | some chars =>
                        simp [copied] at run
                        rcases run with ⟨rfl, rfl⟩
                        have resultSafe := primitiveResult_value_invariants reachable (FlatSem.Value.litv (.strLit (.implode chars)))
                          (by simp [findValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [valueHasEval])
                        exact ⟨target, related,
                          by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, copied],
                          resultSafe.1, resultSafe.2⟩

/-- Copying a byte array to a string preserves related states and result invariants. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_copyAw8Str {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .copyAw8Str ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .copyAw8Str) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .copyAw8Str) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .copyAw8Str) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
    | cons second rest =>
      cases rest with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
      | cons third rest =>
        cases rest with
        | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
        | nil =>
          cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
          case loc flag address =>
            cases second <;> try simp at run
            case litv lit =>
              cases lit <;> try simp at run
              case intLit offset =>
                cases third <;> try simp at run
                case litv lit =>
                  cases lit <;> try simp at run
                  case intLit length =>
                    cases lookup : storeLookup address source.refs with
                    | none => simp [lookup] at run
                    | some ref =>
                      cases ref <;> simp [lookup] at run
                      case w8array bytes =>
                        have refsEq := related.2.1
                        cases copied : copyArray (bytes, offset) length none with
                        | none =>
                          simp [copied] at run
                          obtain ⟨targetNext, stateRel, failed, closed, safe⟩ :=
                            boundsFailure_related reachable source target next false result related run
                          exact ⟨targetNext, stateRel,
                            by simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
                              FlatSem.doAppCopy, ← refsEq, lookup, copied] using failed, closed, safe⟩
                        | some chars =>
                          simp [copied] at run
                          rcases run with ⟨rfl, rfl⟩
                          have resultSafe := primitiveResult_value_invariants reachable (FlatSem.Value.litv (.strLit (.implode chars)))
                            (by simp [findValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [valueHasEval])
                          exact ⟨target, related,
                            by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
                              FlatSem.doAppCopy, ← refsEq, lookup, copied], resultSafe.1, resultSafe.2⟩

/-- The unsafe byte-array XOR preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_xorAw8StrUnsafe {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .xorAw8StrUnsafe ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .xorAw8StrUnsafe) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .xorAw8StrUnsafe) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .xorAw8StrUnsafe) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
    | cons second rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
      | nil =>
        cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
        case loc flag address =>
          cases second <;> try simp at run
          case litv lit =>
            cases lit <;> try simp at run
            case strLit str =>
              cases lookup : storeLookup address source.refs with
              | none => simp [lookup] at run
              | some ref =>
                cases ref <;> simp [lookup] at run
                case w8array bytes =>
                  cases xored : xorBytes str.explode bytes with
                  | none => simp [xored] at run
                  | some output =>
                    obtain ⟨assigned, _, stateRel⟩ := byteStoreUpdate_related reachable source target address bytes output related lookup
                    simp [xored, assigned] at run
                    rcases run with ⟨rfl, rfl⟩
                    have resultSafe := primitiveResult_value_invariants reachable FlatSem.unitValue
                      (by simp [FlatSem.unitValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
                      (by simp [FlatSem.unitValue, valueHasEval, valuesHaveEval])
                    refine ⟨{ target with refs := target.refs.set address (.w8array output) }, stateRel, ?_,
                      resultSafe.1, resultSafe.2⟩
                    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
                      FlatSem.doAppCopy, ← related.2.1, lookup, xored, assigned]

/-- Copying a string into a byte array preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_copyStrAw8 {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .copyStrAw8 ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .copyStrAw8) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .copyStrAw8) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .copyStrAw8) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
    | cons second rest =>
      cases rest with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
      | cons third rest =>
        cases rest with
        | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
        | cons fourth rest =>
          cases rest with
          | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
          | cons fifth rest =>
            cases rest with
            | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
            | nil =>
              cases first <;> try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
              case litv lit =>
                cases lit <;> try simp at run
                case strLit str =>
                  cases second <;> try simp at run
                  case litv lit =>
                    cases lit <;> try simp at run
                    case intLit offset =>
                      cases third <;> try simp at run
                      case litv lit =>
                        cases lit <;> try simp at run
                        case intLit length =>
                          cases fourth <;> try simp at run
                          case loc flag address =>
                            cases fifth <;> try simp at run
                            case litv lit =>
                              cases lit <;> try simp at run
                              case intLit dstOffset =>
                                cases lookup : storeLookup address source.refs with
                                | none => simp [lookup] at run
                                | some ref =>
                                  cases ref <;> simp [lookup] at run
                                  case w8array bytes =>
                                    have refsEq := related.2.1
                                    cases copied : copyArray (str.explode, offset) length (some (bytes, dstOffset)) with
                                    | none =>
                                      simp [copied] at run
                                      obtain ⟨targetNext, stateRel, failed, closed, safe⟩ :=
                                        boundsFailure_related reachable source target next false result related run
                                      exact ⟨targetNext, stateRel,
                                        by simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
                                          FlatSem.doAppCopy, ← refsEq, lookup, copied] using failed, closed, safe⟩
                                    | some output =>
                                      obtain ⟨assigned, _, stateRel⟩ := byteStoreUpdate_related reachable source target address bytes output related lookup
                                      simp [copied, assigned] at run
                                      rcases run with ⟨rfl, rfl⟩
                                      have resultSafe := primitiveResult_value_invariants reachable FlatSem.unitValue
                                        (by simp [FlatSem.unitValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
                                        (by simp [FlatSem.unitValue, valueHasEval, valuesHaveEval])
                                      refine ⟨{ target with refs := target.refs.set address (.w8array output) }, stateRel, ?_,
                                        resultSafe.1, resultSafe.2⟩
                                      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
                                        FlatSem.doAppCopy, ← refsEq, lookup, copied, assigned]

/-- Copying between byte arrays preserves the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_copyAw8Aw8 {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .copyAw8Aw8 ≠ .src .opapp)
    (_valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .copyAw8Aw8) [])) reachable)
    (_valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .copyAw8Aw8) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .copyAw8Aw8) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
    | cons second rest =>
      cases rest with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
      | cons third rest =>
        cases rest with
        | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
        | cons fourth rest =>
          cases rest with
          | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
          | cons fifth rest =>
            cases rest with
            | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
            | nil =>
              cases first <;> try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
              case loc sourceFlag sourceAddress =>
                cases second <;> try simp at run
                case litv lit =>
                  cases lit <;> try simp at run
                  case intLit offset =>
                    cases third <;> try simp at run
                    case litv lit =>
                      cases lit <;> try simp at run
                      case intLit length =>
                        cases fourth <;> try simp at run
                        case loc flag address =>
                          cases fifth <;> try simp at run
                          case litv lit =>
                            cases lit <;> try simp at run
                            case intLit dstOffset =>
                              cases sourceLookup : storeLookup sourceAddress source.refs with
                              | none => simp [sourceLookup] at run
                              | some sourceRef =>
                                cases sourceRef <;> try simp [sourceLookup] at run
                                case w8array sourceBytes =>
                                  cases lookup : storeLookup address source.refs with
                                  | none => simp [lookup] at run
                                  | some ref =>
                                    cases ref <;> simp [lookup] at run
                                    case w8array bytes =>
                                      have refsEq := related.2.1
                                      cases copied : copyArray (sourceBytes, offset) length (some (bytes, dstOffset)) with
                                      | none =>
                                        simp [copied] at run
                                        obtain ⟨targetNext, stateRel, failed, closed, safe⟩ :=
                                          boundsFailure_related reachable source target next false result related run
                                        exact ⟨targetNext, stateRel,
                                          by simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
                                            FlatSem.doAppCopy, ← refsEq, sourceLookup, lookup, copied] using failed, closed, safe⟩
                                      | some output =>
                                        obtain ⟨assigned, _, stateRel⟩ := byteStoreUpdate_related reachable source target address bytes output related lookup
                                        simp [copied, assigned] at run
                                        rcases run with ⟨rfl, rfl⟩
                                        have resultSafe := primitiveResult_value_invariants reachable FlatSem.unitValue
                                          (by simp [FlatSem.unitValue, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain])
                                          (by simp [FlatSem.unitValue, valueHasEval, valuesHaveEval])
                                        refine ⟨{ target with refs := target.refs.set address (.w8array output) }, stateRel, ?_,
                                          resultSafe.1, resultSafe.2⟩
                                        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
                                          FlatSem.doAppCopy, ← refsEq, sourceLookup, lookup, copied, assigned]

end Flapjack.Compiler.Backend.FlatElim
