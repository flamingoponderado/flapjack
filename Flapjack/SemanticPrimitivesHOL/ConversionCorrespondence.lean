import Flapjack.SemanticPrimitivesHOL.NumericConversion
import Flapjack.SemanticPrimitivesHOL.ApplyNumericCore

/-! The computable numeric dispatcher agrees with HOL's guarded conversion. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- On a singleton argument, the executable conversion dispatcher equals the
original type check followed by the HOL conversion. This Flapjack bridge has no
separate HOL declaration. -/
theorem doAppNumericCore_fromTo {σ : Type} (state : Store Value × HolFfiState σ)
    (source target : PrimType) (v : Value) :
    doAppNumericCore state (.fromTo source target) [v] =
      some (if checkType source v then
        (doConversion v source target).map (fun result =>
          match result with
          | .inl error => (state, .err (.raise error))
          | .inr value => (state, .val value))
        else none) := by
  cases source <;> try (rename_i width; cases width)
  all_goals cases target <;> try (rename_i width; cases width)
  all_goals cases v with
    | litv lit =>
      cases lit with
      | intLit i =>
        simp [doAppNumericCore, doConversion, checkType, theLitvInt] <;>
          split <;> simp_all <;>
          (have ha := Int.natAbs_of_nonneg (show 0 ≤ i by omega)
           have ht := Int.toNat_of_nonneg (show 0 ≤ i by omega)
           congr 1
           omega)
      | _ =>
        simp [doAppNumericCore, doConversion, checkType, theLitvWord8,
          theLitvWord64, theLitvFloat64, theLitvChar, charToWord8, word8ToChar]
    | _ =>
      simp [doAppNumericCore, doConversion] <;> simp [checkType]

end Flapjack.SemanticPrimitivesHOL
