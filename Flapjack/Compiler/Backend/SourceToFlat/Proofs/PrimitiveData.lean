import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveArray
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ThunkRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ListConversion

/-! Data operation simulation for the source-to-flat primitive proof. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- A successful string subscript has string and integer operands. -/
theorem strsub_operands {F : Type} (source : State F) (string index : Value)
    (successful : doApp (source.refs, source.ffi) .strsub [string, index] ≠ none) :
    ∃ str n, string = .litv (.strLit str) ∧ index = .litv (.intLit n) := by
  cases string <;> cases index <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case litv.litv strLit intLit =>
    cases strLit <;> cases intLit <;> simp at successful
    case strLit.intLit str n => exact ⟨str, n, rfl, rfl⟩

/-- String subscripting yields related characters or related bounds exceptions. -/
theorem strsub_complete_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (ok : genvCOk genv.c)
    (str : Flapjack.Basis.Pure.MlString.MlString) (index : Int) :
    match doApp (source.refs, source.ffi) .strsub [.litv (.strLit str), .litv (.intLit index)],
      FlatSem.doAppData flat .strsub [.litv (.strLit str), .litv (.intLit index)] with
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ nextFlat = flat ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  have exceptionRel := (valueRel_lemmas genv ok).2.2.2.2
  by_cases negative : index < 0
  · simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData, SemanticPrimitivesHOL.readIndexed,
      FlatSem.readIndexed, SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, negative, ResultRel.raise exceptionRel]
  · cases element : str.explode[index.toNat]? with
    | none => simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData, SemanticPrimitivesHOL.readIndexed,
        FlatSem.readIndexed, SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, negative, element, ResultRel.raise exceptionRel]
    | some char => simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData, SemanticPrimitivesHOL.readIndexed,
        FlatSem.readIndexed, negative, element, ResultRel.value (ValueRel.literal genv (.char char))]

/-- A vector subscript without type error has vector and integer operands. -/
theorem vsub_operands {F : Type} (source : State F) (vector index : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .vsubUnsafe else .vsub) [vector, index] ≠ none) :
    ∃ values n, vector = .vectorv values ∧ index = .litv (.intLit n) := by
  cases unsafeOp <;> cases vector <;> cases index <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i values lit
  all_goals cases lit <;> simp at successful
  all_goals rename_i n
  all_goals exact ⟨values, n, rfl, rfl⟩

/-- Related vectors return related elements or agree on bounds behavior. -/
theorem vsub_complete_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (ok : genvCOk genv.c)
    (values : List Value) (flatValues : List FlatSem.Value) (related : List.Forall₂ (ValueRel genv) values flatValues)
    (index : Int) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.vsubUnsafe else .vsub
    match doApp (source.refs, source.ffi) op [.vectorv values, .litv (.intLit index)],
      FlatSem.doAppData flat op [.vectorv flatValues, .litv (.intLit index)] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ nextFlat = flat ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  have exceptionRel := (valueRel_lemmas genv ok).2.2.2.2
  have pairRel := forall₂_lookupRel related index.toNat
  by_cases negative : index < 0
  · cases unsafeOp <;> simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData,
      SemanticPrimitivesHOL.readIndexed, FlatSem.readIndexed, SemanticPrimitivesHOL.boundsFailure,
      FlatSem.boundsFailure, negative, ResultRel.raise exceptionRel]
  · cases src : values[index.toNat]? with
    | none =>
      cases dst : flatValues[index.toNat]? with
      | none => cases unsafeOp <;> simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData,
          SemanticPrimitivesHOL.readIndexed, FlatSem.readIndexed, SemanticPrimitivesHOL.boundsFailure,
          FlatSem.boundsFailure, negative, src, dst, ResultRel.raise exceptionRel]
      | some value => simp [src, dst, Flapjack.optionRel] at pairRel
    | some value =>
      cases dst : flatValues[index.toNat]? with
      | none => simp [src, dst, Flapjack.optionRel] at pairRel
      | some flatValue =>
        simp only [src, dst, Flapjack.optionRel] at pairRel
        cases unsafeOp <;> simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData,
          SemanticPrimitivesHOL.readIndexed, FlatSem.readIndexed, negative, src, dst, ResultRel.value pairRel]

/-- A non-type-error byte-array slice identifies its source store cell. -/
theorem copyAw8Str_operands {F : Type} (source : State F) (first second third : Value)
    (successful : doApp (source.refs, source.ffi) .copyAw8Str [first, second, third] ≠ none) :
    ∃ flag address offset length bytes, first = .loc flag address ∧ second = .litv (.intLit offset) ∧
      third = .litv (.intLit length) ∧ storeLookup address source.refs = some (.w8array bytes) := by
  cases first <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc flag address =>
    cases second <;> try simp at successful
    case litv secondLit =>
      cases secondLit <;> try simp at successful
      case intLit offset =>
        cases third <;> try simp at successful
        case litv thirdLit =>
          cases thirdLit <;> try simp at successful
          case intLit length =>
            cases lookup : storeLookup address source.refs with
            | none => simp [lookup] at successful
            | some cell =>
              cases cell with
              | w8array bytes => exact ⟨flag, address, offset, length, bytes, rfl, rfl, rfl, lookup⟩
              | refv value => simp [lookup] at successful
              | varray values => simp [lookup] at successful
              | thunk mode value => simp [lookup] at successful

/-- Byte-array slicing preserves normal and bounds-error results at the
shifted flat-store address. -/
theorem copyAw8Str_complete_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (states : StateRel genv source flat)
    (ok : genvCOk genv.c) (flag : Bool) (address : Nat) (bytes : List (BitVec 8))
    (lookup : storeLookup address source.refs = some (.w8array bytes)) (offset length : Int) :
    match doApp (source.refs, source.ffi) .copyAw8Str
        [.loc flag address, .litv (.intLit offset), .litv (.intLit length)],
      FlatSem.doAppCopy flat .copyAw8Str
        [.loc flag (address + 1), .litv (.intLit offset), .litv (.intLit length)] with
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ nextFlat = flat ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  have flatLookup := stateRel_byteArray_lookup genv source flat states address bytes lookup
  have exceptionRel := (valueRel_lemmas genv ok).2.2.2.2
  cases copied : copyArray (bytes, offset) length none with
  | none => simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppCopy, lookup, flatLookup,
      SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, copied, ResultRel.raise exceptionRel]
  | some chars => simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppCopy, lookup, flatLookup, copied,
      ResultRel.value (ValueRel.literal genv _)]

/-- A non-type-error XOR operation identifies the byte array and XOR result. -/
theorem xorAw8Str_operands {F : Type} (source : State F) (first second : Value)
    (successful : doApp (source.refs, source.ffi) .xorAw8StrUnsafe [first, second] ≠ none) :
    ∃ flag address text bytes result, first = .loc flag address ∧ second = .litv (.strLit text) ∧
      storeLookup address source.refs = some (.w8array bytes) ∧ xorBytes text.explode bytes = some result := by
  cases first <;> cases second <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc.litv flag address lit =>
    cases lit <;> try simp at successful
    case strLit text =>
      cases lookup : storeLookup address source.refs with
      | none => simp [lookup] at successful
      | some cell =>
        cases cell with
        | w8array bytes =>
          cases xor : xorBytes text.explode bytes with
          | none => simp [lookup, xor] at successful
          | some result => exact ⟨flag, address, text, bytes, result, rfl, rfl, lookup, xor⟩
        | refv value => simp [lookup] at successful
        | varray values => simp [lookup] at successful
        | thunk mode value => simp [lookup] at successful

/-- XOR updates related byte arrays at corresponding addresses. -/
theorem xorAw8Str_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (states : StateRel genv source flat)
    (flag : Bool) (address : Nat) (text : Basis.Pure.MlString.MlString) (bytes result : List (BitVec 8))
    (lookup : storeLookup address source.refs = some (.w8array bytes))
    (xor : xorBytes text.explode bytes = some result) :
    ∃ sourceRefs flatRefs,
      doApp (source.refs, source.ffi) .xorAw8StrUnsafe [.loc flag address, .litv (.strLit text)] =
        some ((sourceRefs, source.ffi), .val (.conv none [])) ∧
      FlatSem.doAppCopy flat .xorAw8StrUnsafe [.loc flag (address + 1), .litv (.strLit text)] =
        some (some ({ flat with refs := flatRefs }, .val FlatSem.unitValue)) ∧
      StateRel genv { source with refs := sourceRefs } { flat with refs := flatRefs } ∧
      flatRefs.take 1 = flat.refs.take 1 := by
  have assigned : storeAssign address (.w8array result) source.refs =
      some (source.refs.set address (.w8array result)) := by
    have indexed : source.refs[address]? = some (.w8array bytes) := lookup
    simp [storeAssign, indexed, storeValueSameType]
  obtain ⟨flatRefs, flatAssigned, reserved, nextRel⟩ :=
    stateRel_storeAssign genv source flat states address (.w8array result) (.w8array result)
      (.w8array result) _ assigned
  have flatLookup := stateRel_byteArray_lookup genv source flat states address bytes lookup
  refine ⟨_, flatRefs, ?_, ?_, nextRel, reserved⟩
  · simp [doApp, doAppNumericCore, doAppBasic, lookup, xor, assigned]
  · simp [FlatSem.doAppCopy, flatLookup, xor, flatAssigned]

/-- A successful thunk allocation preserves related stores and the reserved
flat-store slot. -/
theorem allocThunk_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (states : StateRel genv source flat)
    (mode : ThunkMode) (value : Value) (flatValue : FlatSem.Value) (related : ValueRel genv value flatValue)
    (successful : doApp (source.refs, source.ffi) (.thunkOp (.allocThunk mode)) [value] ≠ none) :
    let sourceAlloc := storeAlloc (.thunk mode value) source.refs
    let flatAlloc := storeAlloc (.thunk mode flatValue) flat.refs
    doApp (source.refs, source.ffi) (.thunkOp (.allocThunk mode)) [value] =
      some ((sourceAlloc.1, source.ffi), .val (.loc false sourceAlloc.2)) ∧
    FlatSem.doAppData flat (.thunkOp (.allocThunk mode)) [flatValue] =
      some (some ({ flat with refs := flatAlloc.1 }, .val (.loc false flatAlloc.2))) ∧
    ValueRel genv (.loc false sourceAlloc.2) (.loc false flatAlloc.2) ∧
    StateRel genv { source with refs := sourceAlloc.1 } { flat with refs := flatAlloc.1 } ∧
    flatAlloc.1.take 1 = flat.refs.take 1 := by
  have guard : SemanticPrimitivesHOL.badThunkUpdate mode value source.refs = false := by
    cases h : SemanticPrimitivesHOL.badThunkUpdate mode value source.refs with
    | false => rfl
    | true => simp [doApp, doAppNumericCore, doAppBasic, thunkOp, h] at successful
  have flatGuard : FlatSem.badThunkUpdate mode flatValue flat.refs = false := by
    rw [← badThunkUpdate_related genv source flat states mode value flatValue related]
    exact guard
  obtain ⟨nextRel, offset, reserved⟩ := stateRel_storeAlloc genv source flat states
    (.thunk mode value) (.thunk mode flatValue) (.thunk mode related)
  dsimp only
  refine ⟨?_, ?_, ?_, nextRel, reserved⟩
  · simp [doApp, doAppNumericCore, doAppBasic, thunkOp, guard]
  · simp [FlatSem.doAppData, flatGuard]
  · rw [offset]
    exact .location genv _ false

/-- A successful explicit thunk update has a non-reference location, passes
its validity guard, and assigns a thunk-compatible store cell. -/
theorem updateThunkOp_operands {F : Type} (source : State F) (mode : ThunkMode) (pointer value : Value)
    (successful : doApp (source.refs, source.ffi) (.thunkOp (.updateThunk mode)) [pointer, value] ≠ none) :
    ∃ address refs, pointer = .loc false address ∧
      SemanticPrimitivesHOL.badThunkUpdate mode value source.refs = false ∧
      storeAssign address (.thunk mode value) source.refs = some refs := by
  cases pointer <;> simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at successful
  case loc flag address =>
    cases flag with
    | true => simp at successful
    | false =>
      cases guard : SemanticPrimitivesHOL.badThunkUpdate mode value source.refs with
      | true => simp [guard] at successful
      | false =>
        cases assigned : storeAssign address (.thunk mode value) source.refs with
        | none => simp [guard, assigned] at successful
        | some refs => exact ⟨address, refs, rfl, rfl, assigned⟩

/-- Explicit thunk update preserves related stores and the reserved flat slot. -/
theorem updateThunkOp_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (states : StateRel genv source flat)
    (mode : ThunkMode) (address : Nat) (value : Value) (flatValue : FlatSem.Value)
    (related : ValueRel genv value flatValue) (sourceRefs : Store Value)
    (guard : SemanticPrimitivesHOL.badThunkUpdate mode value source.refs = false)
    (assigned : storeAssign address (.thunk mode value) source.refs = some sourceRefs) :
    ∃ flatRefs,
      doApp (source.refs, source.ffi) (.thunkOp (.updateThunk mode)) [.loc false address, value] =
        some ((sourceRefs, source.ffi), .val (.conv none [])) ∧
      FlatSem.doAppData flat (.thunkOp (.updateThunk mode)) [.loc false (address + 1), flatValue] =
        some (some ({ flat with refs := flatRefs }, .val FlatSem.unitValue)) ∧
      StateRel genv { source with refs := sourceRefs } { flat with refs := flatRefs } ∧
      flatRefs.take 1 = flat.refs.take 1 := by
  have flatGuard : FlatSem.badThunkUpdate mode flatValue flat.refs = false := by
    rw [← badThunkUpdate_related genv source flat states mode value flatValue related]
    exact guard
  obtain ⟨flatRefs, flatAssigned, reserved, nextRel⟩ :=
    stateRel_storeAssign genv source flat states address (.thunk mode value) (.thunk mode flatValue)
      (.thunk mode related) sourceRefs assigned
  refine ⟨flatRefs, ?_, ?_, nextRel, reserved⟩
  · simp [doApp, doAppNumericCore, doAppBasic, thunkOp, guard, assigned]
  · simp [FlatSem.doAppData, flatGuard, flatAssigned]

/-- A non-type-error string-to-byte-array copy has its five expected operands
and a byte-array destination. -/
theorem copyStrAw8_operands {F : Type} (source : State F) (a b c d e : Value)
    (successful : doApp (source.refs, source.ffi) .copyStrAw8 [a,b,c,d,e] ≠ none) :
    ∃ text offset length flag address dstOffset bytes,
      a = .litv (.strLit text) ∧ b = .litv (.intLit offset) ∧ c = .litv (.intLit length) ∧
      d = .loc flag address ∧ e = .litv (.intLit dstOffset) ∧
      storeLookup address source.refs = some (.w8array bytes) := by
  cases a <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case litv aLit =>
    cases aLit <;> try simp at successful
    case strLit text =>
      cases b <;> try simp at successful
      case litv bLit =>
        cases bLit <;> try simp at successful
        case intLit offset =>
          cases c <;> try simp at successful
          case litv cLit =>
            cases cLit <;> try simp at successful
            case intLit length =>
              cases d <;> try simp at successful
              case loc flag address =>
                cases e <;> try simp at successful
                case litv eLit =>
                  cases eLit <;> try simp at successful
                  case intLit dstOffset =>
                    cases lookup : storeLookup address source.refs with
                    | none => simp [lookup] at successful
                    | some cell =>
                      cases cell with
                      | w8array bytes => exact ⟨text, offset, length, flag, address, dstOffset, bytes, rfl, rfl, rfl, rfl, rfl, lookup⟩
                      | refv value => simp [lookup] at successful
                      | varray values => simp [lookup] at successful
                      | thunk mode value => simp [lookup] at successful

/-- A non-type-error byte-array copy identifies both array cells. -/
theorem copyAw8Aw8_operands {F : Type} (source : State F) (a b c d e : Value)
    (successful : doApp (source.refs, source.ffi) .copyAw8Aw8 [a,b,c,d,e] ≠ none) :
    ∃ srcFlag srcAddress offset length dstFlag dstAddress dstOffset srcBytes dstBytes,
      a = .loc srcFlag srcAddress ∧ b = .litv (.intLit offset) ∧ c = .litv (.intLit length) ∧
      d = .loc dstFlag dstAddress ∧ e = .litv (.intLit dstOffset) ∧
      storeLookup srcAddress source.refs = some (.w8array srcBytes) ∧
      storeLookup dstAddress source.refs = some (.w8array dstBytes) := by
  cases a <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc srcFlag srcAddress =>
    cases b <;> try simp at successful
    case litv bLit =>
      cases bLit <;> try simp at successful
      case intLit offset =>
        cases c <;> try simp at successful
        case litv cLit =>
          cases cLit <;> try simp at successful
          case intLit length =>
            cases d <;> try simp at successful
            case loc dstFlag dstAddress =>
              cases e <;> try simp at successful
              case litv eLit =>
                cases eLit <;> try simp at successful
                case intLit dstOffset =>
                  cases srcLookup : storeLookup srcAddress source.refs with
                  | none => simp [srcLookup] at successful
                  | some srcCell =>
                    cases srcCell with
                    | refv value => simp [srcLookup] at successful
                    | varray values => simp [srcLookup] at successful
                    | thunk mode value => simp [srcLookup] at successful
                    | w8array srcBytes =>
                      cases dstLookup : storeLookup dstAddress source.refs with
                      | none => simp [srcLookup, dstLookup] at successful
                      | some dstCell =>
                        cases dstCell with
                        | refv value => simp [srcLookup, dstLookup] at successful
                        | varray values => simp [srcLookup, dstLookup] at successful
                        | thunk mode value => simp [srcLookup, dstLookup] at successful
                        | w8array dstBytes => exact ⟨srcFlag, srcAddress, offset, length, dstFlag, dstAddress, dstOffset,
                            srcBytes, dstBytes, rfl, rfl, rfl, rfl, rfl, srcLookup, dstLookup⟩

/-- Byte-array copying preserves the original source snapshot even when the
source and destination addresses coincide. -/
theorem copyAw8Aw8_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (states : StateRel genv source flat)
    (ok : genvCOk genv.c) (srcFlag : Bool) (srcAddress : Nat) (srcBytes : List (BitVec 8))
    (offset length : Int) (dstFlag : Bool) (dstAddress : Nat) (dstBytes : List (BitVec 8)) (dstOffset : Int)
    (srcLookup : storeLookup srcAddress source.refs = some (.w8array srcBytes))
    (dstLookup : storeLookup dstAddress source.refs = some (.w8array dstBytes)) :
    match doApp (source.refs, source.ffi) .copyAw8Aw8
        [.loc srcFlag srcAddress, .litv (.intLit offset), .litv (.intLit length), .loc dstFlag dstAddress, .litv (.intLit dstOffset)],
      FlatSem.doAppCopy flat .copyAw8Aw8
        [.loc srcFlag (srcAddress + 1), .litv (.intLit offset), .litv (.intLit length), .loc dstFlag (dstAddress + 1), .litv (.intLit dstOffset)] with
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        ffi = source.ffi ∧ nextFlat = { flat with refs := nextFlat.refs } ∧
        StateRel genv { source with refs := refs } nextFlat ∧ nextFlat.refs.take 1 = flat.refs.take 1 ∧
        ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  have flatSrc := stateRel_byteArray_lookup genv source flat states srcAddress srcBytes srcLookup
  have flatDst := stateRel_byteArray_lookup genv source flat states dstAddress dstBytes dstLookup
  have exceptionRel := (valueRel_lemmas genv ok).2.2.2.2
  cases copied : copyArray (srcBytes, offset) length (some (dstBytes, dstOffset)) with
  | none =>
    simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppCopy, srcLookup, dstLookup, flatSrc, flatDst,
      SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, copied, ResultRel.raise exceptionRel, states]
  | some result =>
    have assigned : storeAssign dstAddress (.w8array result) source.refs =
        some (source.refs.set dstAddress (.w8array result)) := by
      have indexed : source.refs[dstAddress]? = some (.w8array dstBytes) := dstLookup
      simp [storeAssign, indexed, storeValueSameType]
    obtain ⟨flatRefs, flatAssigned, reserved, nextRel⟩ :=
      stateRel_storeAssign genv source flat states dstAddress (.w8array result) (.w8array result)
        (.w8array result) _ assigned
    have resultRel : ValueRel genv (.conv none []) FlatSem.unitValue := .tuple genv [] [] (.nil genv)
    simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppCopy, srcLookup, dstLookup, flatSrc, flatDst, copied,
      assigned, flatAssigned, nextRel, reserved, ResultRel.value resultRel]

/-- Copying a string slice into a byte array has related success and bounds
results, preserving the reserved flat-store slot. -/
theorem copyStrAw8_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (states : StateRel genv source flat)
    (ok : genvCOk genv.c) (text : Basis.Pure.MlString.MlString) (offset length : Int)
    (flag : Bool) (address : Nat) (bytes : List (BitVec 8)) (dstOffset : Int)
    (lookup : storeLookup address source.refs = some (.w8array bytes)) :
    match doApp (source.refs, source.ffi) .copyStrAw8
        [.litv (.strLit text), .litv (.intLit offset), .litv (.intLit length), .loc flag address, .litv (.intLit dstOffset)],
      FlatSem.doAppCopy flat .copyStrAw8
        [.litv (.strLit text), .litv (.intLit offset), .litv (.intLit length), .loc flag (address + 1), .litv (.intLit dstOffset)] with
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        ffi = source.ffi ∧ nextFlat = { flat with refs := nextFlat.refs } ∧
        StateRel genv { source with refs := refs } nextFlat ∧ nextFlat.refs.take 1 = flat.refs.take 1 ∧
        ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  have flatLookup := stateRel_byteArray_lookup genv source flat states address bytes lookup
  have exceptionRel := (valueRel_lemmas genv ok).2.2.2.2
  cases copied : copyArray (text.explode, offset) length (some (bytes, dstOffset)) with
  | none =>
    simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppCopy, lookup, flatLookup,
      SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, copied, ResultRel.raise exceptionRel, states]
  | some result =>
    have assigned : storeAssign address (.w8array result) source.refs =
        some (source.refs.set address (.w8array result)) := by
      have indexed : source.refs[address]? = some (.w8array bytes) := lookup
      simp [storeAssign, indexed, storeValueSameType]
    obtain ⟨flatRefs, flatAssigned, reserved, nextRel⟩ :=
      stateRel_storeAssign genv source flat states address (.w8array result) (.w8array result)
        (.w8array result) _ assigned
    have resultRel : ValueRel genv (.conv none []) FlatSem.unitValue := .tuple genv [] [] (.nil genv)
    simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppCopy, lookup, flatLookup, copied,
      assigned, flatAssigned, nextRel, reserved, ResultRel.value resultRel]

end Flapjack.Compiler.Backend.SourceToFlat
