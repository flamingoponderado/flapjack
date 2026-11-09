module

public import Flapjack.Compiler.Backend.FlatPattern.BindingsTotal
public import Flapjack.Compiler.Backend.FlatPattern.NaiveTotal
public import Flapjack.Compiler.Backend.FlatPattern.Encode
public import Flapjack.Compiler.Backend.FlatPattern.Decode
public import Flapjack.Compiler.Backend.PatternComp.Decision
public import Flapjack.Misc.Sptree.FromList

@[expose] public section

/-! Branch lowering for the flat pattern compiler. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon

/-- Build the indexed branch table used by the flat pattern compiler. -/
def branchTree (branches : List FlatLang.Exp) : Spt FlatLang.Exp :=
  sptFromList branches

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

/-- Branch compilation in the source's indexed-map and sparse-tree shape. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_pats_def"]
theorem compilePats_source (cfg : Config) (naive : Bool) (t : Tra) (i : Nat)
    (v default : FlatLang.Exp) (ps : List (FlatLang.Pat × FlatLang.Exp)) :
    compilePats cfg naive t i v default ps =
      let branches := ps.map (compilePatRhs t i v)
      if naive then
        naivePatternMatches t v (List.zip (ps.map Prod.fst) branches) default
      else
        let pats := ps.mapIdx (fun j (p, _) => (encodePat p, j))
        decodeDtree t (sptFromList branches) v default (PatternComp.comp pats) := by
  simp only [compilePats, branchTree, List.mapIdx_eq_zipIdx_map]

end Flapjack.Compiler.Backend.FlatPattern
