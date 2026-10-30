import Flapjack.Compiler.Backend.BviToData.Assign
import Flapjack.Compiler.Backend.Bvi.Budget
import Flapjack.Compiler.Backend.BviToData.Optimise

/-! Checked expression traversal for BVI-to-data lowering. -/
namespace Flapjack.Compiler.Backend.BviToData

private def isVariablesFrom : List Bvi.Exp → Nat → Bool
  | [], _ => true
  | .var v :: xs, n => v == n && isVariablesFrom xs (n + 1)
  | _ :: _, _ => false

private def isTailReturn (rets : Nat) : Bvi.Exp → Bool
  | .return xs => xs.length == rets && isVariablesFrom xs 0
  | _ => false

mutual
/-- Bounded rendering of the source singleton traversal. Exhaustion is
explicit; a sufficient structural bound is proved in `Proofs.Total`.
Correspondence to the HOL traversal remains to be reviewed. -/
def compileFuel : Nat → Nat → List Nat → Bool → List Nat → Bvi.Exp → Option (DataLang.Prog × Nat × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, n, env, tail, live, exp =>
    match exp with
    | .var v =>
        let var := env[v]?.getD 0
        if tail then some (.return [var], n, n + 1)
        else some (.skip, var, max n (var + 1))
    | .ifThenElse x y z => do
        let (cx, vx, n) ← compileFuel fuel n env false live x
        let (cy, vy, n) ← compileFuel fuel n env tail live y
        let (cz, vz, n) ← compileFuel fuel n env tail live z
        let branch := if tail then DataLang.Prog.ifThenElse vx cy cz
          else .ifThenElse vx (.seq cy (.move n vy)) (.seq cz (.move n vz))
        pure (.seq cx branch, n, n + 1)
    | .let xs body => do
        let (c, vs, n) ← compileListFuel fuel n env live xs
        let (body, v, n) ← compileFuel fuel n (vs ++ env) tail live body
        pure (.seq c body, v, n)
    | .raise x => do
        let (c, v, n) ← compileFuel fuel n env false live x
        pure (.seq c (.raise v), v, n)
    | .return xs => do
        let (c, vs, n) ← compileListFuel fuel n env live xs
        pure (.seq c (.return vs), n, n + 1)
    | .op op xs => do
        let (c, vs, n) ← compileListFuel fuel n env live xs
        let c := DataLang.Prog.seq c (iAssign n op vs.reverse live env)
        pure (if tail then .seq c (.return [n]) else c, n, n + 1)
    | .tick x => do
        let (c, v, n) ← compileFuel fuel n env tail live x
        pure (.seq .tick c, v, n)
    | .force loc v =>
        let var := env[v]?.getD 0
        let ret := if tail then none else some (n, namesOfList (live ++ env))
        some (.force ret loc var, n, max (n + 1) (var + 1))
    | .call ticks dest xs none => do
        let (c, vs, n) ← compileListFuel fuel n env live xs
        let ret := if tail then none else some ([n], namesOfList (live ++ env))
        pure (.seq c (DataLang.mkTicks ticks (.call ret dest vs none)), n, n + 1)
    | .call ticks dest xs (some handler) => do
        let (c, vs, n) ← compileListFuel fuel n env live xs
        let (h, v, n2) ← compileFuel fuel (n + 1) (n :: env) false live handler
        let ret := some ([n2], namesOfList (live ++ env))
        let after := if tail then DataLang.Prog.return [n2] else .skip
        pure (.seq c (DataLang.mkTicks ticks
          (.seq (.call ret dest vs (some (n, .seq h (.move n2 v)))) after)), n2, n2 + 1)
    | .letCall rets ticks dest xs body => do
        let (c, vs, n) ← compileListFuel fuel n env live xs
        if isTailReturn rets body then
          pure (.seq c (DataLang.mkTicks ticks (.call none (some dest) vs none)), n, n + 1)
        else
          let rs := (List.range rets).map (n + ·)
          let (body, v, n2) ← compileFuel fuel (n + rets) (rs ++ env) tail live body
          let ret := some (rs, namesOfList (live ++ env))
          pure (.seq (.seq c (DataLang.mkTicks ticks (.call ret (some dest) vs none))) body, v, n2)

/-- Bounded traversal of operands with the original live-variable order. -/
def compileListFuel : Nat → Nat → List Nat → List Nat → List Bvi.Exp → Option (DataLang.Prog × List Nat × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, n, _, _, [] => some (.skip, [], n)
  | fuel + 1, n, env, live, x :: xs => do
      let (c, v, n) ← compileFuel fuel n env false live x
      match xs with
      | [] => pure (c, [v], n)
      | _ :: _ =>
          let (rest, vs, n) ← compileListFuel fuel n env (v :: live) xs
          pure (.seq c rest, v :: vs, n)
end

/-- Run the source optimization sequence after checked expression lowering. -/
def compileExpFuel (fuel argc : Nat) (exp : Bvi.Exp) : Option DataLang.Prog := do
  let (prog, _, _) ← compileFuel fuel argc (List.range argc) true [] exp
  pure (optimise prog)

/-- Preserve successful calls at the supplied fuel, retrying with a structural
bound if they exhaust it. Other pipeline stages retain their own bounds. -/
def compileExpBounded (fuel argc : Nat) (exp : Bvi.Exp) : Option DataLang.Prog :=
  match compileExpFuel fuel argc exp with
  | some result => some result
  | none => compileExpFuel (max fuel (Bvi.expBudget exp + 1)) argc exp

end Flapjack.Compiler.Backend.BviToData
