import Flapjack.Compiler.Backend.BvlConst

/-! The original polymorphic suffix-list interface for constant extraction. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl

/-- Extract a cheap binding, shifting variable aliases by the suffix length. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "extract_def"]
def extractSource {α : Type} (e : Exp) (suffix : List α) : Option Exp :=
  match e with
  | .var n => some (.var (n + suffix.length + 1))
  | .op (.intOp (.const n)) _ => some (.op (.intOp (.const n)) [])
  | .op (.blockOp (.cons t)) [] => some (.op (.blockOp (.cons t)) [])
  | _ => none

/-- The production environment builder uses the original extraction on each
suffix. This equation is Flapjack correspondence infrastructure. -/
theorem extractList_cons (x : Exp) (xs : List Exp) :
    extractList (x :: xs) = extractSource x xs :: extractList xs := by
  cases x <;> rfl

end Flapjack.Compiler.Backend.BvlConst
