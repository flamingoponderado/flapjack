import Flapjack.Compiler.Backend.BviLet.Helpers

/-! Checked BVI let optimization. -/
namespace Flapjack.Compiler.Backend.BviLet

/-- Bounded form of the source let optimizer. Fuel exhaustion is explicit;
the bound and the connection to the source's total definition remain to be
proved. -/
def compileFuel : Nat → List Nat → Nat → Bvi.Exp → Option Bvi.Exp
  | 0, _, _, _ => none
  | fuel + 1, env, d, exp =>
    let compile := compileFuel fuel env d
    match exp with
    | .var v => some (.var (v + (env[v]?.getD d)))
    | .ifThenElse x y z => do
        pure (.ifThenElse (← compile x) (← compile y) (← compile z))
    | .let xs body =>
        match xs with
        | [] => compile body
        | _ :: _ => do
          let k := xs.length - 1
          match body with
          | .var v =>
              if v = k then do
                let last ← xs.getLast?
                let earlier ← xs.dropLast.mapM compile
                let tail ← compileFuel fuel (env.map (k + ·)) (d + k) last
                pure (.let earlier tail)
              else do
                let ys ← xs.mapM compile
                let tail ← compileFuel fuel (extractList ys ++ env) d body
                pure (.let (ys.map deleteVar) tail)
          | _ => do
              let ys ← xs.mapM compile
              let tail ← compileFuel fuel (extractList ys ++ env) d body
              pure (.let (ys.map deleteVar) tail)
    | .raise x => do pure (.raise (← compile x))
    | .tick x => do pure (.tick (← compile x))
    | .force loc v => some (.force loc (v + env[v]?.getD d))
    | .op op xs => do pure (.op op (← xs.mapM compile))
    | .call ticks dest xs handler => do
        let args ← xs.mapM compile
        let handler ← handler.mapM (compileFuel fuel (0 :: env) d)
        pure (.call ticks dest args handler)
    | .return xs => do pure (.return (← xs.mapM compile))
    | .letCall rets ticks dest xs body => do
        let args ← xs.mapM compile
        let body ← compileFuel fuel (List.replicate rets 0 ++ env) d body
        pure (.letCall rets ticks dest args body)

end Flapjack.Compiler.Backend.BviLet
