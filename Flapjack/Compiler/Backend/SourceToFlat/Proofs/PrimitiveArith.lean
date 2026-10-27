import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyNumeric

/-! Integer and word primitive simulation over preliminary factored relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- A successful integer primitive application has exactly two integer
literal operands. This inversion is infrastructure for expression simulation. -/
theorem integerArith_operands {F : Type} (source : SemanticPrimitivesHOL.State F)
    (action : Arith) (values : List SemanticPrimitivesHOL.Value)
    (successful : doApp (source.refs, source.ffi) (.arith action .intT) values ≠ none) :
    ∃ left right, values = [.litv (.intLit left), .litv (.intLit right)] := by
  simp only [doApp, doAppNumericCore] at successful
  cases values with
  | nil => simp at successful
  | cons first rest =>
    cases rest with
    | nil => simp at successful
    | cons second rest =>
      cases rest with
      | cons third rest => simp at successful
      | nil =>
        cases first <;> try simp at successful
        case litv lit =>
          cases lit <;> try simp at successful
          case intLit left =>
            cases second <;> try simp at successful
            case litv lit =>
              cases lit <;> try simp at successful
              case intLit right => exact ⟨left, right, rfl⟩

/-- A successful Word8 primitive application has exactly two word
literal operands. This inversion is infrastructure for expression simulation. -/
theorem word8Arith_operands {F : Type} (source : SemanticPrimitivesHOL.State F)
    (action : Arith) (values : List SemanticPrimitivesHOL.Value)
    (successful : doApp (source.refs, source.ffi) (.arith action (.wordT .w8)) values ≠ none) :
    ∃ left right, values = [.litv (.word8 left), .litv (.word8 right)] := by
  simp only [doApp, doAppNumericCore] at successful
  cases values with
  | nil => simp at successful
  | cons first rest =>
    cases rest with
    | nil => simp at successful
    | cons second rest =>
      cases rest with
      | cons third rest => simp at successful
      | nil =>
        cases first <;> try simp at successful
        case litv lit =>
          cases lit <;> try simp at successful
          case word8 left =>
            cases second <;> try simp at successful
            case litv lit =>
              cases lit <;> try simp at successful
              case word8 right => exact ⟨left, right, rfl⟩

/-- A successful Word64 primitive application has exactly two word
literal operands. This inversion is infrastructure for expression simulation. -/
theorem word64Arith_operands {F : Type} (source : SemanticPrimitivesHOL.State F)
    (action : Arith) (values : List SemanticPrimitivesHOL.Value)
    (successful : doApp (source.refs, source.ffi) (.arith action (.wordT .w64)) values ≠ none) :
    ∃ left right, values = [.litv (.word64 left), .litv (.word64 right)] := by
  simp only [doApp, doAppNumericCore] at successful
  cases values with
  | nil => simp at successful
  | cons first rest =>
    cases rest with
    | nil => simp at successful
    | cons second rest =>
      cases rest with
      | cons third rest => simp at successful
      | nil =>
        cases first <;> try simp at successful
        case litv lit =>
          cases lit <;> try simp at successful
          case word64 left =>
            cases second <;> try simp at successful
            case litv lit =>
              cases lit <;> try simp at successful
              case word64 right => exact ⟨left, right, rfl⟩

/-- Integer arithmetic on literal operands preserves successful values and the
Div exception, without changing either store or FFI state. This is Flapjack
infrastructure over the factored value relation, not a reviewed HOL theorem. -/
theorem integerArith_related {C F : Type} (genv : GlobalEnv) (ok : genvCOk genv.c)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (action : Arith) (left right : Int) :
    match doApp (source.refs, source.ffi) (.arith action .intT)
        [.litv (.intLit left), .litv (.intLit right)],
      FlatSem.doAppNumeric flat (.arith action .intT)
        [.litv (.intLit left), .litv (.intLit right)] with
    | none, some none => True
    | some ((refs, ffi), sourceResult), some (some (flatNext, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ flatNext = flat ∧
          ResultRel ValueRel genv sourceResult flatResult
    | _, _ => False := by
  by_cases zero : right = 0 <;> cases action <;>
    simp [doApp, doAppNumericCore, FlatSem.doAppNumeric,
      FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat, zero]
  all_goals first | exact ResultRel.value (.literal genv _) | exact ResultRel.raise (exceptionValues_related genv ok).1

/-- Word8 arithmetic preserves literal results and rejects the same unsupported
operations, without changing either state. This is Flapjack infrastructure
using the preliminary value relation. -/
theorem word8Arith_related {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (action : Arith) (left right : BitVec 8) :
    match doApp (source.refs, source.ffi) (.arith action (.wordT .w8))
        [.litv (.word8 left), .litv (.word8 right)],
      FlatSem.doAppNumeric flat (.arith action (.wordT .w8))
        [.litv (.word8 left), .litv (.word8 right)] with
    | none, some none => True
    | some ((refs, ffi), sourceResult), some (some (flatNext, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ flatNext = flat ∧
          ResultRel ValueRel genv sourceResult flatResult
    | _, _ => False := by
  cases action <;> simp [doApp, doAppNumericCore, FlatSem.doAppNumeric,
    FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat]
  all_goals simp [SemanticPrimitivesHOL.wordArith]
  all_goals exact ResultRel.value (.literal genv _)

/-- Word64 arithmetic preserves literal results and rejects the same unsupported
operations, without changing either state. This is Flapjack infrastructure
using the preliminary value relation. -/
theorem word64Arith_related {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (action : Arith) (left right : BitVec 64) :
    match doApp (source.refs, source.ffi) (.arith action (.wordT .w64))
        [.litv (.word64 left), .litv (.word64 right)],
      FlatSem.doAppNumeric flat (.arith action (.wordT .w64))
        [.litv (.word64 left), .litv (.word64 right)] with
    | none, some none => True
    | some ((refs, ffi), sourceResult), some (some (flatNext, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ flatNext = flat ∧
          ResultRel ValueRel genv sourceResult flatResult
    | _, _ => False := by
  cases action <;> simp [doApp, doAppNumericCore, FlatSem.doAppNumeric,
    FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat]
  all_goals simp [SemanticPrimitivesHOL.wordArith]
  all_goals exact ResultRel.value (.literal genv _)


/-- Successful Word8 shifts have a single word operand. -/
theorem word8Shift_operand {F : Type} (source : SemanticPrimitivesHOL.State F)
    (shift : Shift) (amount : Nat) (operand : SemanticPrimitivesHOL.Value)
    (successful : doApp (source.refs, source.ffi) (.shift .w8 shift amount) [operand] ≠ none) :
    ∃ word, operand = .litv (.word8 word) := by
  simp only [doApp, doAppNumericCore, doAppBasic] at successful
  cases operand <;> simp at successful
  case litv lit =>
    cases lit <;> simp at successful
    case word8 word => exact ⟨word, rfl⟩

/-- The two primitive dispatchers agree on a Word8 shift and preserve both
states. This is infrastructure over the preliminary factored relation. -/
theorem word8Shift_related {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (shift : Shift) (amount : Nat) (word : BitVec 8) :
    doApp (source.refs, source.ffi) (.shift .w8 shift amount) [.litv (.word8 word)] =
      some ((source.refs, source.ffi), .val (.litv (.word8 (shift8Lookup shift word amount)))) ∧
    FlatSem.doAppNumeric flat (.shift .w8 shift amount) [.litv (.word8 word)] =
      some (some (flat, .val (.litv (.word8 (shift8Lookup shift word amount))))) ∧
    ValueRel genv (.litv (.word8 (shift8Lookup shift word amount)))
      (.litv (.word8 (shift8Lookup shift word amount))) := by
  refine ⟨?_, ?_, .literal genv _⟩
  · simp [doApp, doAppNumericCore, doAppBasic]
  · simp [FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue,
      doApp, doAppNumericCore, doAppBasic, FlatSem.valueToFlat]

/-- Successful Word64 shifts have a single word operand. -/
theorem word64Shift_operand {F : Type} (source : SemanticPrimitivesHOL.State F)
    (shift : Shift) (amount : Nat) (operand : SemanticPrimitivesHOL.Value)
    (successful : doApp (source.refs, source.ffi) (.shift .w64 shift amount) [operand] ≠ none) :
    ∃ word, operand = .litv (.word64 word) := by
  simp only [doApp, doAppNumericCore, doAppBasic] at successful
  cases operand <;> simp at successful
  case litv lit =>
    cases lit <;> simp at successful
    case word64 word => exact ⟨word, rfl⟩

/-- The two primitive dispatchers agree on a Word64 shift and preserve both
states. This is infrastructure over the preliminary factored relation. -/
theorem word64Shift_related {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (shift : Shift) (amount : Nat) (word : BitVec 64) :
    doApp (source.refs, source.ffi) (.shift .w64 shift amount) [.litv (.word64 word)] =
      some ((source.refs, source.ffi), .val (.litv (.word64 (shift64Lookup shift word amount)))) ∧
    FlatSem.doAppNumeric flat (.shift .w64 shift amount) [.litv (.word64 word)] =
      some (some (flat, .val (.litv (.word64 (shift64Lookup shift word amount))))) ∧
    ValueRel genv (.litv (.word64 (shift64Lookup shift word amount)))
      (.litv (.word64 (shift64Lookup shift word amount))) := by
  refine ⟨?_, ?_, .literal genv _⟩
  · simp [doApp, doAppNumericCore, doAppBasic]
  · simp [FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue,
      doApp, doAppNumericCore, doAppBasic, FlatSem.valueToFlat]

/-- Successful primitive conversions consume a literal operand. -/
theorem conversion_operand {F : Type} (source : SemanticPrimitivesHOL.State F)
    (fromType toType : PrimType) (operand : SemanticPrimitivesHOL.Value)
    (successful : doApp (source.refs, source.ffi) (.fromTo fromType toType) [operand] ≠ none) :
    ∃ lit, operand = .litv lit := by
  cases operand with
  | litv lit => exact ⟨lit, rfl⟩
  | _ =>
    cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;>
      simp [doApp, doAppNumericCore] at successful

/-- Source and flat conversions agree on literals, including `Chr` failures.
This is infrastructure over the preliminary factored relation. -/
theorem conversion_related {C F : Type} (genv : GlobalEnv) (ok : genvCOk genv.c)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (fromType toType : PrimType) (lit : Lit) :
    match doApp (source.refs, source.ffi) (.fromTo fromType toType) [.litv lit],
      FlatSem.doAppNumeric flat (.fromTo fromType toType) [.litv lit] with
    | none, some none => True
    | some ((refs, ffi), sourceResult), some (some (flatNext, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ flatNext = flat ∧
          ResultRel ValueRel genv sourceResult flatResult
    | _, _ => False := by
  cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;> cases lit
  case intT.charT.intLit n =>
    by_cases bad : n < 0 ∨ n > 255 <;>
      simp [doApp, doAppNumericCore, FlatSem.doAppNumeric,
        FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat, bad]
    · exact ResultRel.raise (exceptionValues_related genv ok).2.1
    · exact ResultRel.value (.literal genv _)
  all_goals simp [doApp, doAppNumericCore, FlatSem.doAppNumeric,
    FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat]
  all_goals exact ResultRel.value (.literal genv _)

end Flapjack.Compiler.Backend.SourceToFlat
