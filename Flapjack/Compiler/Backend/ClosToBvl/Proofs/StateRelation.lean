import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ValueRelation
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Oracle
import Flapjack.Compiler.Backend.ClosToBvl.Stubs

/-! Reference cells and initialization data for the closure-to-BVL state relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Related mutable arrays, thunks and byte arrays have the same source shape. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ref_rel_def"]
def refRel {α β : Type} (R : α → β → Prop) : ClosSem.Ref α → BvlSem.Ref β → Prop
  | .valueArray xs, .valueArray ys => List.Forall₂ R xs ys
  | .thunk m x, .thunk n y => m = n ∧ R x y
  | .byteArray xs, .byteArray frozen ys => frozen = false ∧ xs = ys
  | _, _ => False

/-- Code pointers for every possible partial application. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "global_table_def"]
def globalTable (maxApp : Nat) : BvlSem.Value :=
  .block 0 (((List.range maxApp).map fun total =>
    (List.range total).map fun previous =>
      BvlSem.Value.codePtr (partialAppFnLocation maxApp total previous)).flatten)

/-- The three source-reference cases, expressed by the shape of their BVL cells. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ref_rel_simp"]
theorem refRel_simp {α β : Type} (R : α → β → Prop)
    (vs : List α) (m : AstHOL.ThunkMode) (v : α) (bs : List (BitVec 8))
    (y : BvlSem.Ref β) :
    (refRel R (.valueArray vs) y ↔ ∃ ws, y = .valueArray ws ∧ List.Forall₂ R vs ws) ∧
    (refRel R (.thunk m v) y ↔ ∃ w, y = .thunk m w ∧ R v w) ∧
    (refRel R (.byteArray bs) y ↔ y = .byteArray false bs) := by
  cases y <;> simp [refRel, eq_comm]

end Flapjack.Compiler.Backend.ClosToBvl
