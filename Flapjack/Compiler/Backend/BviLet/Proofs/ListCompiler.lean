module

public import Flapjack.Compiler.Backend.BviLet.SourceList
public import Flapjack.HolRef

@[expose] public section

/-! List equations used by the BVI let correctness proof. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs

/-- Implication premises may be exchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "IMP_COMM"]
theorem impComm (b1 b2 b3 : Prop) : (b1 → b2 → b3) ↔ (b2 → b1 → b3) := by
  constructor <;> intro h a b <;> exact h b a

/-- The original compiler preserves list append. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "compile_APPEND"]
theorem compileAppend (xs ys : List Bvi.Exp) (ax : List Nat) (d : Nat) :
    BviLet.compile ax d (xs ++ ys) = BviLet.compile ax d xs ++ BviLet.compile ax d ys := by
  simp only [BviLet.compile_eq_compileList]
  induction xs with
  | nil => simp [BviLet.compileList]
  | cons x xs ih => simp [BviLet.compileList, ih]

/-- A cons is compiled as a singleton followed by the remaining list. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "compile_CONS"]
theorem compileCons (ax : List Nat) (d : Nat) (x : Bvi.Exp) (xs : List Bvi.Exp) :
    BviLet.compile ax d (x :: xs) = BviLet.compile ax d [x] ++ BviLet.compile ax d xs := by
  simpa using compileAppend [x] xs ax d

end Flapjack.Compiler.Backend.BviLet.Proofs
