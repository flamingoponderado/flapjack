import Flapjack.Compiler.Backend.BvlToBvi.CompileOp
import Flapjack.Compiler.Backend.BviLet.Compile

/-! Checked BVL-to-BVI expression conversion. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

private abbrev Aux := List (Nat × Nat × Bvi.Exp)

private def compileAuxFuel (fuel k args : Nat) (body : Bvi.Exp) : Option Aux := do
  let body ← BviLet.compileFuel fuel [] 0 body
  pure [(bvlNumStubs + bvlToBviNamespaces * k + 1, args, body)]

mutual
/-- Bounded form of expression conversion. Auxiliary code uses a flattened
list in place of HOL's `SmartAppend` tree. Both traversal and BVI optimizer
fuel may be exhausted; proofs of sufficient bounds and HOL correspondence are
still required before this can be used as the total production pass. -/
def compileFuel : Nat → Nat → Nat → Bvl.Exp → Option (Bvi.Exp × Aux × Nat)
  | 0, _, _, _ => none
  | fuel + 1, optFuel, n, exp =>
    match exp with
    | .var v => some (.var v, [], n)
    | .ifThenElse x y z => do
        let (x, a, n) ← compileFuel fuel optFuel n x
        let (y, b, n) ← compileFuel fuel optFuel n y
        let (z, c, n) ← compileFuel fuel optFuel n z
        pure (.ifThenElse x y z, a ++ b ++ c, n)
    | .let xs body =>
        if xs.isEmpty then do
          let (args, inner) := destLet body
          let (args, a, n) ← compileListFuel fuel optFuel n args
          let (inner, b, n) ← compileFuel fuel optFuel n inner
          let extra ← compileAuxFuel optFuel n args.length inner
          pure (.call 0 (some (bvlNumStubs + bvlToBviNamespaces * n + 1)) args none,
            a ++ b ++ extra, n + 1)
        else do
          let (args, a, n) ← compileListFuel fuel optFuel n xs
          let (body, b, n) ← compileFuel fuel optFuel n body
          pure (.let args body, a ++ b, n)
    | .raise x => do
        let (x, aux, n) ← compileFuel fuel optFuel n x
        pure (.raise x, aux, n)
    | .tick x => do
        let (x, aux, n) ← compileFuel fuel optFuel n x
        pure (.tick x, aux, n)
    | .force loc v => some (.force (bvlNumStubs + bvlToBviNamespaces * loc) v, [], n)
    | .op op xs => do
        let (xs, aux, n) ← compileListFuel fuel optFuel n xs
        pure (compileOp op xs, aux, n)
    | .handle x y => do
        let (args, inner) := destLet x
        let (args, a, n) ← compileListFuel fuel optFuel n args
        let (inner, b, n) ← compileFuel fuel optFuel n inner
        let (y, c, n) ← compileFuel fuel optFuel n y
        let extra ← compileAuxFuel optFuel n args.length inner
        pure (.call 0 (some (bvlNumStubs + bvlToBviNamespaces * n + 1)) args (some y),
          a ++ b ++ c ++ extra, n + 1)
    | .call ticks dest xs => do
        let (xs, aux, n) ← compileListFuel fuel optFuel n xs
        pure (.call ticks (dest.map fun loc => bvlNumStubs + bvlToBviNamespaces * loc) xs none, aux, n)

/-- Bounded list traversal, threading the fresh-code counter in source order. -/
def compileListFuel : Nat → Nat → Nat → List Bvl.Exp → Option (List Bvi.Exp × Aux × Nat)
  | 0, _, _, _ => none
  | _ + 1, _, n, [] => some ([], [], n)
  | fuel + 1, optFuel, n, x :: xs => do
      let (x, a, n) ← compileFuel fuel optFuel n x
      let (xs, b, n) ← compileListFuel fuel optFuel n xs
      pure (x :: xs, a ++ b, n)
end

/-- Compile one labeled function and its auxiliary functions. The BVI let
optimization and expression conversion share the explicit checked bounds. -/
def compileSingleFuel (fuel optFuel n : Nat) (p : Nat × Nat × Bvl.Exp) :
    Option (List (Nat × Nat × Bvi.Exp) × Nat) := do
  let (name, args, exp) := p
  let (exp, aux, n) ← compileFuel fuel optFuel n exp
  let exp ← BviLet.compileFuel optFuel [] 0 exp
  pure ((bvlNumStubs + bvlToBviNamespaces * name, args, exp) :: aux, n)

/-- Compile a sequence of labeled functions, preserving source code order. -/
def compileProgramsFuel (fuel optFuel : Nat) : Nat → List (Nat × Nat × Bvl.Exp) →
    Option (List (Nat × Nat × Bvi.Exp) × Nat)
  | n, [] => some ([], n)
  | n, p :: ps => do
      let (code, n) ← compileSingleFuel fuel optFuel n p
      let (rest, n) ← compileProgramsFuel fuel optFuel n ps
      pure (code ++ rest, n)

/-- Incremental compilation exposes the next fresh name before the code. -/
def compileIncFuel (fuel optFuel n : Nat) (prog : List (Nat × Nat × Bvl.Exp)) :
    Option (Nat × List (Nat × Nat × Bvi.Exp)) := do
  let (code, n) ← compileProgramsFuel fuel optFuel n prog
  pure (n, code)

end Flapjack.Compiler.Backend.BvlToBvi
