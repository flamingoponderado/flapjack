import Flapjack.Compiler.Backend.BvlConst.Compile
import Flapjack.Misc.ListEl

/-! Source entry points for total BVL constant propagation. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl
private instance : Nonempty Exp := ⟨.var 0⟩

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

open Classical in
/-- Constructor clauses of the original list recursion. These equations are
comparison evidence for `compile_def`, not a separate HOL declaration. -/
theorem compile_singleton_equations (env : List (Option Exp)) :
    (∀ v, compile env [.var v] =
      [match env[v]? with
       | some (some (.var i)) => .var (v + i)
       | some (some x) => x
       | _ => .var v]) ∧
    (∀ x y z, compile env [.ifThenElse x y z] =
      (let x := Flapjack.holHd (compile env [x])
       let y := Flapjack.holHd (compile env [y])
       let z := Flapjack.holHd (compile env [z])
       if x = bool true then [y] else if x = bool false then [z]
       else [.ifThenElse x y z])) ∧
    (∀ xs y, compile env [.let xs y] =
      (let ys := compile env xs
       [.let (ys.map deleteVar) (Flapjack.holHd (compile (extractList ys ++ env) [y]))])) ∧
    (∀ x y, compile env [.handle x y] =
      [.handle (Flapjack.holHd (compile env [x]))
        (Flapjack.holHd (compile (none :: env) [y]))]) ∧
    (∀ x, compile env [.raise x] = [.raise (Flapjack.holHd (compile env [x]))]) ∧
    (∀ op xs, compile env [.op op xs] = [smartOp op (compile env xs)]) ∧
    (∀ x, compile env [.tick x] = [.tick (Flapjack.holHd (compile env [x]))]) ∧
    (∀ loc v, compile env [.force loc v] =
      [match env[v]? with
       | some (some (.var i)) => .force loc (v + i)
       | _ => .force loc v]) ∧
    (∀ ticks dest xs, compile env [.call ticks dest xs] = [.call ticks dest (compile env xs)]) := by
  classical
  simp only [compile, compileList, Flapjack.holHd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    cases h : env[v]? with
    | none => simp [compileSing, h]
    | some value =>
      cases value with
      | none => simp [compileSing, h]
      | some e => cases e <;> simp [compileSing, h]
  · intro x y z
    simp only [compileSing]
    split <;> simp_all [bool]
  · intros; simp only [compileSing]
  · intros; simp [compileSing]
  · intros; simp [compileSing]
  · intros; simp [compileSing]
  · intros; simp [compileSing]
  · intro loc v
    cases h : env[v]? with
    | none => simp [compileSing, h]
    | some value =>
      cases value with
      | none => simp [compileSing, h]
      | some e => cases e <;> simp [compileSing, h]
  · intros; simp [compileSing]

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
