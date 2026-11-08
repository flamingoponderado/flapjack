import Flapjack.Compiler.Backend.BvlConst.Compile

/-! Source entry points for total BVL constant propagation. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl

/-- HOL's list traversal, using its equivalent singleton-list formulation. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "compile_def"]
abbrev compile : List (Option Exp) → List Exp → List Exp := compileList

/-- Relate the list and singleton traversals as in the original script. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "compile_eq"]
theorem compile_eq :
    (∀ e env, compile env [e] = [compileSing env e]) ∧
    (∀ es env, compile env es = compileList env es) := by
  constructor
  · intro e env
    simp [compile, compileList]
  · intro es env
    rfl

/-- Check the source list clauses for the shared traversal. -/
theorem compile_list_equations (env : List (Option Exp)) (x y : Exp) (xs : List Exp) :
    compile env [] = [] ∧
      compile env (x :: y :: xs) = compile env [x] ++ compile env (y :: xs) := by
  simp [compile, compileList]

/-- Propagate constants through one expression from an empty environment. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "compile_exp_def"]
def compileExp (e : Exp) : Exp :=
  match compile [] [e] with
  | x :: _ => x
  | [] => .var 0

/-- The single-expression entry point equals the singleton traversal. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "compile_exp_eq"]
theorem compileExp_eq (e : Exp) : compileExp e = compileSing [] e := by
  simp [compileExp, compile, compileList]

end Flapjack.Compiler.Backend.BvlConst
