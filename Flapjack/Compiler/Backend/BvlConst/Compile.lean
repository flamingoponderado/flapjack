import Flapjack.Compiler.Backend.BvlConst

/-! Total singleton and list traversal for BVL constant propagation. The
executed traversal agrees by `Proofs/CompileProduction`. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl

mutual
/-- Propagate the constant environment through a single expression. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "compile_sing_def"]
def compileSing (env : List (Option Exp)) : Exp → Exp
  | .var v =>
      match env[v]? with
      | some (some (.var i)) => .var (v + i)
      | some (some x) => x
      | _ => .var v
  | .ifThenElse x y z =>
      let x := compileSing env x
      let y := compileSing env y
      let z := compileSing env z
      match x with
      | .op (.blockOp (.cons 1)) [] => y
      | .op (.blockOp (.cons 0)) [] => z
      | _ => .ifThenElse x y z
  | .let xs y =>
      let xs := compileList env xs
      .let (xs.map deleteVar) (compileSing (extractList xs ++ env) y)
  | .handle x y => .handle (compileSing env x) (compileSing (none :: env) y)
  | .raise x => .raise (compileSing env x)
  | .op op xs => smartOp op (compileList env xs)
  | .tick x => .tick (compileSing env x)
  | .force loc v =>
      match env[v]? with
      | some (some (.var i)) => .force loc (v + i)
      | _ => .force loc v
  | .call t dest xs => .call t dest (compileList env xs)
termination_by e => sizeOf e

/-- Propagate the same environment through an expression list. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "compile_sing_def"]
def compileList (env : List (Option Exp)) : List Exp → List Exp
  | [] => []
  | x :: xs => compileSing env x :: compileList env xs
termination_by xs => sizeOf xs
end

end Flapjack.Compiler.Backend.BvlConst
