module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Eval
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Pattern extraction used by the source-to-flat Eval compilation case. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

instance evalPatternInst1 : Nonempty FlatSem.Value := ⟨.conv none []⟩

namespace OracleInvariant

/-- Expose the six operands used by the Eval proof. This Flapjack helper has
no separate HOL declaration. -/
theorem list_length_six {α : Type} (xs : List α) (length : xs.length = 6) :
    ∃ a b c d e f, xs = [a, b, c, d, e, f] := by
  cases xs with
  | nil => simp at length
  | cons a xs =>
    cases xs with
    | nil => simp at length
    | cons b xs =>
      cases xs with
      | nil => simp at length
      | cons c xs =>
        cases xs with
        | nil => simp at length
        | cons d xs =>
          cases xs with
          | nil => simp at length
          | cons e xs =>
            cases xs with
            | nil => simp at length
            | cons f xs =>
              cases xs with
              | nil => exact ⟨a, b, c, d, e, f, rfl⟩
              | cons _ _ => simp at length

end OracleInvariant

/-- The Eval tuple pattern binds the last two arguments in matching order. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "pmatch_rows_drop_4"]
theorem pmatchRows_dropFour {C F E : Type} (values : List FlatSem.Value)
    (bytes words : VarN) (body : E) (state : FlatSem.State C F)
    (length : values.length = 6) :
    FlatSem.pmatchRows
        [(.pcon none [.pany, .pany, .pany, .pany, .pvar bytes, .pvar words], body)]
        state (.conv none values) =
      .match ([(words, holLast values), (bytes, holEl 4 values)],
        .pcon none [.pany, .pany, .pany, .pany, .pvar bytes, .pvar words], body) := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := OracleInvariant.list_length_six values length
  have compatible : FlatSem.PmatchStampsOk (α := Nat) (β := Nat) none none 6 6 := .tuple 6 6 rfl
  simp [FlatSem.pmatchRows, FlatSem.pmatch, FlatSem.pmatchList, compatible, holLast, holEl, holHd]

/-- The two tuple bindings are the original list after dropping four values. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "drop_4_via_el"]
theorem dropFour_viaEl {α : Type} [Nonempty α] (values : List α) (length : values.length = 6) :
    [holEl 4 values, holLast values] = values.drop 4 := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := OracleInvariant.list_length_six values length
  simp [holEl, holHd, holLast]

end Flapjack.Compiler.Backend.SourceToFlat
