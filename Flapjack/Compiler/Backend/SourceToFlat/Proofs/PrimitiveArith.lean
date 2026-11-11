module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyNumeric

@[expose] public section

/-! Primitive conversion simulation over preliminary factored relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Successful primitive conversions consume a literal operand. -/
theorem conversion_operand {F : Type} (source : SemanticPrimitivesHOL.State F)
    (fromType toType : PrimType) (operand : SemanticPrimitivesHOL.Value)
    (successful : doApp (source.refs, source.ffi) (.fromTo fromType toType) [operand] ≠ none) :
    ∃ lit, operand = .litv lit := by
  rw [doApp_fromTo_core] at successful
  cases operand with
  | litv lit => exact ⟨lit, rfl⟩
  | _ =>
    cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;>
      simp [doAppNumericCore] at successful

/-- Source and flat conversions agree on literals, including `Chr` failures.
This is Flapjack proof infrastructure for the source-to-flat simulation. -/
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
      simp [doApp_fromTo_core, doAppNumericCore, FlatSem.doAppNumeric,
        FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat, bad]
    · exact ResultRel.raise (valueRel_lemmas genv ok).2.2.1
    · exact ResultRel.value (.literal genv _)
  all_goals simp [doApp_fromTo_core, doAppNumericCore, FlatSem.doAppNumeric,
    FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat]
  all_goals exact ResultRel.value (.literal genv _)

end Flapjack.Compiler.Backend.SourceToFlat
