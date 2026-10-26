import Flapjack.Compiler.Backend.FlatPattern.Names
import Flapjack.Misc.Sptree

/-! Pattern variable binding for flat pattern compilation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon

/-- A bounded replay of `compile_pat_bindings`. `none` means the supplied
step budget was exhausted. The original total function and its termination
proof remain open; this helper does not claim to be that declaration. -/
def compilePatBindingsFuel : Nat → Tra → Nat → List (FlatLang.Pat × Nat × FlatLang.Exp) →
    FlatLang.Exp → Option (NumSet × FlatLang.Exp)
  | _, _, _, [], exp => some (.ln, exp)
  | 0, _, _, _ :: _, _ => none
  | fuel + 1, t, i, (p, k, x) :: rest, exp =>
      match p with
      | .pany | .plit _ => compilePatBindingsFuel fuel t i rest exp
      | .pvar s => do
          let (used, exp2) ← compilePatBindingsFuel fuel t i rest exp
          pure (sptInsert k () used, .let_ t (some s) x exp2)
      | .pcon _ ps => do
          let entries := ps.zipIdx.map fun (p, j) =>
            let key := i + 1 + j
            let name := encNumToName key
            ((j, name), (p, key, FlatLang.Exp.varLocal t name))
          let (used, exp2) ← compilePatBindingsFuel fuel t (i + 2 + ps.length)
            (entries.map Prod.snd ++ rest) exp
          let selected := entries.filter (fun (_, (_, key, _)) => (sptLookup key used).isSome)
          let exp3 := selected.foldr (fun ((j, name), _) body =>
            .let_ t (some name) (.app t (.el j) [x]) body) exp2
          let used2 := if selected.isEmpty then used else sptInsert k () used
          pure (used2, exp3)
      | .pas p v => do
          let name := encNumToName (i + 1)
          let (used, exp2) ← compilePatBindingsFuel fuel t (i + 2)
            ((p, i + 1, .varLocal t name) :: rest) exp
          pure (sptInsert k () used, .let_ t (some v) x
            (.let_ t (some name) (.varLocal t v) exp2))
      | .pref p => do
          let name := encNumToName (i + 1)
          let (used, exp2) ← compilePatBindingsFuel fuel t (i + 2)
            ((p, i + 1, .varLocal t name) :: rest) exp
          pure (sptInsert k () used, .let_ t (some name) (.app t (.el 0) [x]) exp2)

/-- Bind variables of one branch using a supplied step budget. -/
def compilePatRhsFuel (fuel : Nat) (t : Tra) (i : Nat) (v : FlatLang.Exp)
    (branch : FlatLang.Pat × FlatLang.Exp) : Option FlatLang.Exp :=
  (compilePatBindingsFuel fuel t (i + 1) [(branch.1, i, v)] branch.2).map Prod.snd

end Flapjack.Compiler.Backend.FlatPattern
