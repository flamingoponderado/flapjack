import Flapjack.Compiler.Backend.BviLet.Helpers
import Flapjack.Compiler.Backend.Bvi.Budget
import Lean.Elab.Tactic.Omega

/-! Total source-shaped BVI let propagation. -/
namespace Flapjack.Compiler.Backend.BviLet
open Bvi

private theorem memberBudget (xs : List Exp) (e : Exp) (member : e ∈ xs) :
    expBudget e < listBudget xs := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    simp only [List.mem_cons] at member
    simp only [listBudget]
    rcases member with rfl | member
    · omega
    · have := ih member; omega

private theorem dropLastBudget (xs : List Exp) : listBudget xs.dropLast ≤ listBudget xs := by
  induction xs with
  | nil => simp [listBudget]
  | cons x xs ih =>
    cases xs with
    | nil => simp [listBudget]
    | cons y ys => simp only [List.dropLast, listBudget] at *; omega

mutual
/-- Source-shaped total single-expression optimizer. Agreement with the
executed traversal is proved for sufficiently large fuel; the arbitrary-fuel
production path remains open. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "compile_sing_def"]
def compileSing (env : List Nat) (d : Nat) : Exp → Exp
  | .var v => .var (v + (env[v]?.getD d))
  | .ifThenElse x y z => .ifThenElse (compileSing env d x) (compileSing env d y) (compileSing env d z)
  | .let [] body => compileSing env d body
  | .let (x :: xs) body =>
    let bindings := x :: xs
    let k := bindings.length - 1
    match body with
    | .var v =>
      if v = k then
        .let (compileList env d bindings.dropLast)
          (compileSing (env.map (k + ·)) (d + k) (bindings.getLast (by simp [bindings])))
      else
        let ys := compileList env d bindings
        .let (ys.map deleteVar) (compileSing (extractList ys ++ env) d (.var v))
    | other =>
      let ys := compileList env d bindings
      .let (ys.map deleteVar) (compileSing (extractList ys ++ env) d other)
  | .raise x => .raise (compileSing env d x)
  | .tick x => .tick (compileSing env d x)
  | .force loc v => .force loc (v + env[v]?.getD d)
  | .op op xs => .op op (compileList env d xs)
  | .call ticks dest xs none => .call ticks dest (compileList env d xs) none
  | .call ticks dest xs (some handler) => .call ticks dest (compileList env d xs)
      (some (compileSing (0 :: env) d handler))
  | .return xs => .return (compileList env d xs)
  | .letCall rets ticks dest xs body => .letCall rets ticks dest (compileList env d xs)
      (compileSing (List.replicate rets 0 ++ env) d body)
termination_by exp => expBudget exp
decreasing_by
  all_goals try simp only [expBudget, listBudget]
  all_goals try (have := dropLastBudget (x :: xs))
  all_goals try (have := memberBudget (x :: xs) ((x :: xs).getLast (by simp)) (List.getLast_mem (by simp)))
  all_goals try simp only [listBudget] at *
  all_goals try (cases body <;> simp [expBudget] at * <;> omega)
  all_goals try (cases handler <;> simp [expBudget] at * <;> omega)
  all_goals omega

/-- Source-shaped total traversal of expression lists. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "compile_sing_def"]
def compileList (env : List Nat) (d : Nat) : List Exp → List Exp
  | [] => []
  | x :: xs => compileSing env d x :: compileList env d xs
termination_by xs => listBudget xs
decreasing_by all_goals simp only [listBudget] <;> omega
end

end Flapjack.Compiler.Backend.BviLet
