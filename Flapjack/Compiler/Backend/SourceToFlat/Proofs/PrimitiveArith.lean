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


end Flapjack.Compiler.Backend.SourceToFlat
