import Flapjack.Compiler.Backend.FlatLang

/-! The flat-to-closure pass assumes pattern matches have been compiled. -/
namespace Flapjack.Compiler.Backend.FlatProps

mutual
/-- Recognize expressions on which flat-to-closure pattern handling is valid. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "no_Mat_def"]
def noMat : FlatLang.Exp → Bool
  | .raise _ e => noMat e
  | .lit .. | .varLocal .. => true
  | .con _ _ es | .app _ _ es => noMatList es
  | .fn _ _ e => noMat e
  | .if_ _ a b c => noMat a && noMat b && noMat c
  | .let_ _ _ a b => noMat a && noMat b
  | .mat .. => false
  | .handle _ e [(.pvar _, handler)] => noMat e && noMat handler
  | .handle .. => false
  | .letrec _ funs e => noMatFuns funs && noMat e
termination_by e => sizeOf e

/-- Expression-list helper for the recursive no-match predicate. -/
def noMatList : List FlatLang.Exp → Bool
  | [] => true
  | e :: es => noMat e && noMatList es
termination_by es => sizeOf es

/-- Recursive-function helper for the no-match predicate. -/
def noMatFuns : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp) → Bool
  | [] => true
  | (_, _, e) :: es => noMat e && noMatFuns es
termination_by es => sizeOf es
end

/-- Every declaration satisfies the no-match predicate. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "no_Mat_decs_def"]
def noMatDecs : List FlatLang.Exp → Bool
  | [] => true
  | e :: es => noMat e && noMatDecs es

/-- The recursive helper agrees with the list-wide predicate. -/
theorem noMatList_eq_all (es : List FlatLang.Exp) : noMatList es = es.all noMat := by
  induction es with
  | nil => simp [noMatList]
  | cons e es ih => simp [noMatList, ih]

/-- Declaration and expression-list checks use the same predicate. -/
theorem noMatDecs_eq_noMatList (es : List FlatLang.Exp) : noMatDecs es = noMatList es := by
  induction es with
  | nil => simp [noMatDecs, noMatList]
  | cons e es ih => simp [noMatDecs, noMatList, ih]

end Flapjack.Compiler.Backend.FlatProps
