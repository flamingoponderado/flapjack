import Flapjack.Compiler.Backend.BvlHandle

/-! Total source-shaped singleton and list handler compilation. The executed
bounded traversal is proved equal in `Proofs/CompileProduction`. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl DbVars

mutual
/-- Compile one BVL expression while accounting for live variables. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_sing_def"]
def compileSing (limit env : Nat) : Exp → Exp × DbVarSet × Nat × Bool
  | .var v =>
      if v < env then (.var v, .var v, 1, true)
      else (.op (.intOp (.const 0)) [], .empty, 1, true)
  | .ifThenElse x y z =>
      let (x, lx, sx, nx) := compileSing limit env x
      let (y, ly, sy, ny) := compileSing limit env y
      let (z, lz, sz, nz) := compileSing limit env z
      optionalLetLetSing (.ifThenElse x y z) env (mkUnion lx (mkUnion ly lz))
        (sx + sy + sz + 1) limit (nx && ny && nz)
  | .let xs body =>
      if xs.isEmpty then compileSing limit env body
      else
        let (ys, lx, sx, nx) := compileList limit env xs
        let (body, ly, sy, ny) := compileSing limit (env + xs.length) body
        optionalLetLetSing (.let ys body) env (mkUnion lx (.shift xs.length ly))
          (sx + sy + 1) limit (nx && ny)
  | .handle x y =>
      let (x, lx, sx, nx) := compileSing limit env x
      if nx then (x, lx, sx, true) else
        let (y, ly, sy, ny) := compileSing limit (env + 1) y
        (.handle (letLet env (dbToSet lx) x) y, mkUnion lx (.shift 1 ly), sy, ny)
  | .raise x =>
      let (x, live, size, _) := compileSing limit env x
      optionalLetLetSing (.raise x) env live (size + 1) limit false
  | .op op xs =>
      let (ys, live, size, nr) := compileList limit env xs
      match op with
      | .thunkOp .forceThunk => (.op op ys, live, size + 1, false)
      | _ => optionalLetLetSing (.op op ys) env live (size + 1) limit nr
  | .tick x =>
      let (x, live, size, nr) := compileSing limit env x
      (.tick x, live, size, nr)
  | .force m v =>
      if v < env then (.force m v, .var v, 1, false)
      else (.op (.intOp (.const 0)) [], .empty, 1, true)
  | .call ticks dest xs =>
      let (ys, live, size, _) := compileList limit env xs
      optionalLetLetSing (.call ticks dest ys) env live (size + 1) limit false
termination_by e => sizeOf e

/-- Compile a list, combining live variables and sizes in source order. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_sing_def"]
def compileList (limit env : Nat) : List Exp → List Exp × DbVarSet × Nat × Bool
  | [] => ([], .empty, 0, true)
  | x :: xs =>
      let (x, lx, sx, nx) := compileSing limit env x
      let (xs, ly, sy, ny) := compileList limit env xs
      (x :: xs, mkUnion lx ly, sx + sy, nx && ny)
termination_by xs => sizeOf xs
end

end Flapjack.Compiler.Backend.BvlHandle
