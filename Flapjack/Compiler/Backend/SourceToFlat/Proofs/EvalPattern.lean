import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch
import Flapjack.Compiler.Backend.Semantics.FlatSem.Eval
import Flapjack.Misc.ListEl

/-! Pattern extraction used by the source-to-flat Eval compilation case. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

private instance : Nonempty FlatSem.Value := ⟨.conv none []⟩

private theorem lengthSix {α : Type} (values : List α) (length : values.length = 6) :
    ∃ a b c d e f, values = [a, b, c, d, e, f] := by
  cases values with
  | nil => simp at length
  | cons a values =>
    cases values with
    | nil => simp at length
    | cons b values =>
      cases values with
      | nil => simp at length
      | cons c values =>
        cases values with
        | nil => simp at length
        | cons d values =>
          cases values with
          | nil => simp at length
          | cons e values =>
            cases values with
            | nil => simp at length
            | cons f values =>
              cases values with
              | nil => exact ⟨a, b, c, d, e, f, rfl⟩
              | cons _ _ => simp at length

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
  obtain ⟨a, b, c, d, e, f, rfl⟩ := lengthSix values length
  have compatible : FlatSem.PmatchStampsOk (α := Nat) (β := Nat) none none 6 6 := .tuple 6 6 rfl
  simp [FlatSem.pmatchRows, FlatSem.pmatch, FlatSem.pmatchList, compatible, holLast, holEl, holHd]

/-- The two tuple bindings are the original list after dropping four values. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "drop_4_via_el"]
theorem dropFour_viaEl {α : Type} [Nonempty α] (values : List α) (length : values.length = 6) :
    [holEl 4 values, holLast values] = values.drop 4 := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := lengthSix values length
  simp [holEl, holHd, holLast]

/-- The two bindings selected by the compiled Eval pattern are precisely the
arguments consumed by a successful flat Eval callback. -/
theorem evalPattern_matches_doEval {C F E : Type} (values : List FlatSem.Value)
    (bytes words : VarN) (body : E) (state : FlatSem.State C F)
    (decs : List FlatLang.Exp) (next : FlatSem.InstallConfig C) (result : FlatSem.Value)
    (length : values.length = 6)
    (decoded : FlatSem.doEval (values.drop 4) state.evalConfig = some (decs, next, result)) :
    FlatSem.pmatchRows
        [(.pcon none [.pany, .pany, .pany, .pany, .pvar bytes, .pvar words], body)]
        state (.conv none values) =
      .match ([(words, holLast values), (bytes, holEl 4 values)],
        .pcon none [.pany, .pany, .pany, .pany, .pvar bytes, .pvar words], body) ∧
    FlatSem.doEval [holEl 4 values, holLast values] state.evalConfig = some (decs, next, result) := by
  exact ⟨pmatchRows_dropFour values bytes words body state length,
    (dropFour_viaEl values length).symm ▸ decoded⟩

end Flapjack.Compiler.Backend.SourceToFlat
