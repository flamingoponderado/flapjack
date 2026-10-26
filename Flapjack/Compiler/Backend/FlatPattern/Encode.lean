import Flapjack.Compiler.Backend.FlatPattern.Decode

/-! Convert flat patterns to the input representation of the pattern compiler. -/
namespace Flapjack.Compiler.Backend.FlatPattern

mutual
/-- Drop bound variable names and type-group identifiers exactly as the source
pattern compiler does, retaining constructor tags and their sibling arities. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "encode_pat_def"]
def encodePat : FlatLang.Pat → PatternSemantics.Pat
  | .pany | .pvar _ => .any
  | .plit l => .lit l
  | .pcon tag ps =>
      let encoded := tag.map fun (i, group) => (i, group.map Prod.snd)
      .cons encoded (encodePats ps)
  | .pas p _ => encodePat p
  | .pref p => .ref (encodePat p)

/-- Traverse child patterns in their source order. -/
def encodePats : List FlatLang.Pat → List PatternSemantics.Pat
  | [] => []
  | p :: ps => encodePat p :: encodePats ps
end

end Flapjack.Compiler.Backend.FlatPattern
