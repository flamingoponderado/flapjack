module

public import Flapjack.SemanticPrimitivesHOL.NumericConversion
public import Flapjack.SemanticPrimitivesHOL.Primitives
public import Flapjack.SemanticPrimitivesHOL.Conversions

@[expose] public section

/-! Type preservation for the source primitive conversion. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- A successful primitive conversion has the requested result type. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "do_conversion_check_type"]
theorem doConversion_checkType (v : Value) (source target : PrimType) (result : Value)
    (converted : doConversion v source target = some (.inr result)) : checkType target result = true := by
  cases source <;> try (rename_i width; cases width)
  all_goals cases target <;> try (rename_i width; cases width)
  all_goals simp [doConversion] at converted
  all_goals try (split at converted <;> simp_all)
  all_goals cases converted <;> rfl

/-- Every primitive type is one of the seven source alternatives. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "prim_type_cases"]
theorem primType_cases (ty : PrimType) :
    ty = .boolT ∨ ty = .intT ∨ ty = .charT ∨ ty = .strT ∨
      ty = .wordT .w8 ∨ ty = .wordT .w64 ∨ ty = .float64T := by
  cases ty
  all_goals try simp
  rename_i size
  cases size
  all_goals simp

/-- The natural-number value encoding is injective. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "nat_to_v_11"]
theorem natToValue_inj (i j : Nat) : natToValue i = natToValue j ↔ i = j := by
  simp [natToValue]
  exact ⟨Int.ofNat.inj, fun same => by rw [same]⟩

end Flapjack.SemanticPrimitivesProps
