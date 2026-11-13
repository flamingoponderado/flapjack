module

public import Flapjack.Compiler.Backend.Bvl.Syntax
public import Flapjack.Compiler.Backend.Bvi.Syntax
public import Flapjack.Compiler.Backend.BvlToBvi.Budget

@[expose] public section

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

/-- Count global allocations with the original list-shaped recursion. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "alloc_glob_count_def"]
def allocGlobCount : List Bvl.Exp → Nat
  | [] => 0
  | x :: y :: xs => allocGlobCount [x] + allocGlobCount (y :: xs)
  | [.var _] => 0
  | [.ifThenElse x y z] => allocGlobCount [x] + allocGlobCount [y] + allocGlobCount [z]
  | [.handle x y] => allocGlobCount [x] + allocGlobCount [y]
  | [.tick x] | [.raise x] => allocGlobCount [x]
  | [.force _ _] => 0
  | [.let xs x] => allocGlobCount (x :: xs)
  | [.call _ _ xs] => allocGlobCount xs
  | [.op (.globOp .allocGlobal) xs] => 1 + allocGlobCount xs
  | [.op _ xs] => allocGlobCount xs
termination_by xs => listBudget xs
decreasing_by
  all_goals simp_all [listBudget, expBudget]
  all_goals try (cases xs <;> simp_all [listBudget])
  all_goals omega

/-- The mutually recursive traversal and the original list recursion count
the same global allocations. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "alloc_glob_count_eq_global_count_list"]
theorem allocGlobCount_eq_globalCountList :
    (∀ e, globalCountSing e = allocGlobCount [e]) ∧
      (∀ es, globalCountList es = allocGlobCount es) := by
  have listEq (xs : List Bvl.Exp) : globalCountList xs = allocGlobCount xs := by
    fun_induction allocGlobCount xs <;> simp_all [globalCountList, globalCountSing]
  refine ⟨?_, listEq⟩
  intro e
  simpa [globalCountList] using listEq [e]

end Flapjack.Compiler.Backend.BvlToBvi
