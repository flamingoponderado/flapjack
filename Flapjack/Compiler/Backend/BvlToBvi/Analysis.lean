import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Compiler.Backend.Bvi.Syntax

/-! BVL analyses and literal lowering used by the BVL-to-BVI pass. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- Decompose a BVL let, using the source's fallback for other expressions. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "destLet_def"]
def destLet : Bvl.Exp → List Bvl.Exp × Bvl.Exp
  | .let xs b => (xs, b)
  | _ => ([], .var 0)

/-- Use the small-integer operation inside the original inclusive bound. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_int_def"]
def compileInt (i : Int) : Bvi.Exp :=
  .op (if -268435457 ≤ i ∧ i ≤ 268435457 then .intOp (.const i)
    else .blockOp (.build [.int i])) []

mutual
/-- Count global allocation operations in one BVL expression. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "global_count_sing_def"]
def globalCountSing : Bvl.Exp → Nat
  | .var _ | .force _ _ => 0
  | .ifThenElse x y z => globalCountSing x + globalCountSing y + globalCountSing z
  | .handle x y => globalCountSing x + globalCountSing y
  | .tick x | .raise x => globalCountSing x
  | .let xs x => globalCountSing x + globalCountList xs
  | .call _ _ xs => globalCountList xs
  | .op (.globOp .allocGlobal) xs => 1 + globalCountList xs
  | .op _ xs => globalCountList xs

/-- Count global allocations across a list, in source order. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "global_count_sing_def"]
def globalCountList : List Bvl.Exp → Nat
  | [] => 0
  | x :: xs => globalCountSing x + globalCountList xs
end

end Flapjack.Compiler.Backend.BvlToBvi
