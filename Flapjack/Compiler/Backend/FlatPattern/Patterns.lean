import Flapjack.Compiler.Backend.FlatPattern.Bindings
import Flapjack.Compiler.Backend.FlatPattern.BindingsTotal
import Flapjack.Compiler.Backend.FlatPattern.NaiveTotal
import Flapjack.Compiler.Backend.FlatPattern.Encode
import Flapjack.Compiler.Backend.FlatPattern.Decode
import Flapjack.Compiler.Backend.PatternComp.Decision

/-! Bounded execution of the flat pattern compiler's branch lowering. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon

/-- Bounded replay of `naive_pattern_match`; exhausted fuel is reported. -/
def naivePatternMatchFuel : Nat → Tra → List (FlatLang.Pat × FlatLang.Exp) → Option FlatLang.Exp
  | _, t, [] => some (FlatLang.mkBool t true)
  | 0, _, _ :: _ => none
  | fuel + 1, t, (p, v) :: rest =>
      match p with
      | .pany | .pvar _ => naivePatternMatchFuel fuel t rest
      | .plit l => do
          let tail ← naivePatternMatchFuel fuel t rest
          pure (FlatLang.smartIf t (.app t (.src .equality) [v, .lit t l]) tail (FlatLang.mkBool t false))
      | .pcon tag ps => do
          let children := ps.zipIdx.map fun (p, i) => (p, FlatLang.Exp.app t (.el i) [v])
          let tail ← naivePatternMatchFuel fuel t (children ++ rest)
          match tag with
          | none => pure tail
          | some (tag, _) => pure (FlatLang.smartIf t (.app t (.tagLenEq tag ps.length) [v])
              tail (FlatLang.mkBool t false))
      | .pas p _ => naivePatternMatchFuel fuel t ((p, v) :: rest)
      | .pref p => naivePatternMatchFuel fuel t ((p, .app t (.el 0) [v]) :: rest)

/-- Bounded sequential naive branch matching, preserving branch order. -/
def naivePatternMatchesFuel (fuel : Nat) (t : Tra) (v : FlatLang.Exp) :
    List (FlatLang.Pat × FlatLang.Exp) → FlatLang.Exp → Option FlatLang.Exp
  | [], default => some default
  | (p, x) :: ps, default => do
      let guard ← naivePatternMatchFuel fuel t [(p, v)]
      let rest ← naivePatternMatchesFuel fuel t v ps default
      pure (FlatLang.smartIf t guard x rest)

/-- The source `sptree$fromList` on branch expressions. -/
private def branchTree (branches : List FlatLang.Exp) : Spt FlatLang.Exp :=
  (branches.foldl (fun (state : Nat × Spt FlatLang.Exp) branch =>
    (state.1 + 1, sptInsert state.1 branch state.2)) (0, .ln)).2

/-- Compile pattern branches using the original naive or decision-tree path. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_pats_def"]
def compilePats (_cfg : Config) (naive : Bool) (t : Tra) (i : Nat)
    (v default : FlatLang.Exp) (ps : List (FlatLang.Pat × FlatLang.Exp)) : FlatLang.Exp :=
  let branches := ps.map (compilePatRhs t i v)
  if naive then
    naivePatternMatches t v (List.zip (ps.map Prod.fst) branches) default
  else
    let pats := ps.zipIdx.map fun ((p, _), j) => (encodePat p, j)
    decodeDtree t (branchTree branches) v default (PatternComp.comp pats)

/-- Run the source `compile_pats` algorithm with an explicit budget for naive
matching. `none` reports exhaustion; the original total declaration and a
proof of a sufficient naive-matching bound remain open. -/
def compilePatsFuel (fuel : Nat) (_cfg : Config) (naive : Bool) (t : Tra) (i : Nat)
    (v default : FlatLang.Exp) (ps : List (FlatLang.Pat × FlatLang.Exp)) : Option FlatLang.Exp := do
  let branches := ps.map (compilePatRhs t i v)
  if naive then
    naivePatternMatchesFuel fuel t v (List.zip (ps.map Prod.fst) branches) default
  else
    let pats := ps.zipIdx.map fun ((p, _), j) => (encodePat p, j)
    let tree := PatternComp.comp pats
    pure (decodeDtree t (branchTree branches) v default tree)

end Flapjack.Compiler.Backend.FlatPattern
