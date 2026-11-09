module

public import Flapjack.Compiler.Backend.ClosKnown.Config

@[expose] public section

/-! Source-shaped total approximation merging. The list helper implements the
pairwise traversal used by HOL’s MAP2; it is called on equal-length lists. -/
namespace Flapjack.Compiler.Backend.ClosKnown

mutual
/-- Merge approximations with the source’s constructor and equality tests. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "merge_def" 278]
def mergeHOL : ValApprox → ValApprox → ValApprox
  | .impossible, y => y
  | x, .impossible => x
  | .tuple tag xs, .tuple tag₂ ys =>
      if xs.length == ys.length && tag == tag₂ then
        .tuple tag (mergeListHOL xs ys)
      else .other
  | .closNoInline loc arity, .closNoInline loc₂ arity₂ =>
      if loc == loc₂ && arity == arity₂ then .closNoInline loc arity else .other
  | .clos loc arity body size, .clos loc₂ arity₂ body₂ size₂ =>
      if loc == loc₂ && arity == arity₂ && body == body₂ && size == size₂ then
        .clos loc arity body size
      else .other
  | .int x, .int y => if x == y then .int x else .other
  | _, _ => .other
termination_by a _ => sizeOf a
decreasing_by all_goals simp_wf <;> omega

/-- Pairwise merge, used only after the input lengths agree. -/
def mergeListHOL : List ValApprox → List ValApprox → List ValApprox
  | x :: xs, y :: ys => mergeHOL x y :: mergeListHOL xs ys
  | _, _ => []
termination_by xs _ => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

/-- The helper traverses the paired elements in the same order as source MAP2.
It is Flapjack infrastructure for the representation of the recursive call. -/
theorem mergeListHOL_eq_zip (xs ys : List ValApprox) :
    mergeListHOL xs ys = (xs.zip ys).map (fun (x, y) => mergeHOL x y) := by
  induction xs generalizing ys with
  | nil => simp [mergeListHOL]
  | cons x xs ih =>
    cases ys with
    | nil => simp [mergeListHOL]
    | cons y ys => simp [mergeListHOL, ih]

end Flapjack.Compiler.Backend.ClosKnown
