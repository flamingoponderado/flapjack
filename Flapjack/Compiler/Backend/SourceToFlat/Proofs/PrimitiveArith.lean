import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyNumeric

/-! Integer primitive simulation over the preliminary factored relations. -/
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

end Flapjack.Compiler.Backend.SourceToFlat
