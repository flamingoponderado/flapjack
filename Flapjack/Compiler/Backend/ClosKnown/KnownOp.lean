import Flapjack.Compiler.Backend.ClosKnown.Merge

/-! Total approximation operation from the known-function optimizer. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- Propagate value approximations through global, constructor and indexing
operations. The list bound witnesses make the source `EL` access explicit. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "known_op_def"]
def knownOpHOL (op : Op) (args : List ValApprox) (globals : Spt ValApprox) : ValApprox × Spt ValApprox :=
  match op, args with
  | .globOp (.global n), [] => ((sptLookup n globals).getD .other, globals)
  | .globOp (.setGlobal n), a :: _ =>
      let value := match sptLookup n globals with
        | none => a
        | some old => mergeHOL old a
      (.other, sptInsert n value globals)
  | .blockOp (.cons tag), _ => (.tuple tag args, globals)
  | .intOp (.const n), _ => (.int n, globals)
  | .memOp .el, [.tuple _ xs, .int i] =>
      if h : 0 ≤ i ∧ i < Int.ofNat xs.length then
        (xs[i.toNat]'((Int.toNat_lt h.1).2 h.2), globals)
      else (.other, globals)
  | .memOp .el, .impossible :: _ => (.impossible, globals)
  | .memOp .el, _ :: .impossible :: _ => (.impossible, globals)
  | _, _ => (.other, globals)

end Flapjack.Compiler.Backend.ClosKnown
