import Flapjack.SemanticPrimitivesHOL.Primitives

/-! Source numeric and byte-string comparisons. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

private def compareResult (op : Opb) (order : Ordering) : Bool :=
  match op, order with
  | .lt, .lt | .gt, .gt => true
  | .leq, .lt | .leq, .eq | .geq, .gt | .geq, .eq => true
  | _, _ => false

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "num_cmp_def"]
def numCmp (op : Opb) (a b : Nat) : Bool := compareResult op (compare a b)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "int_cmp_def"]
def intCmp (op : Opb) (a b : Int) : Bool := compareResult op (compare a b)

private def compareBytes : List HolChar → List HolChar → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: xs, b :: ys =>
    match compare a.toNat b.toNat with
    | .eq => compareBytes xs ys
    | order => order

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "str_cmp_def"]
def strCmp (fast : Bool) (op : Opb) (a b : MlString) : Bool :=
  let a := a.explode
  let b := b.explode
  let order := if fast && a.length != b.length then compare a.length b.length else compareBytes a b
  compareResult op order

end Flapjack.SemanticPrimitivesHOL
