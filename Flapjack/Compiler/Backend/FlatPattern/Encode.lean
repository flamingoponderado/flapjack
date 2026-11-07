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

/-- The child-pattern helper implements the source's `MAP encode_pat`. -/
theorem encodePats_eq_map (ps : List FlatLang.Pat) : encodePats ps = ps.map encodePat := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [encodePats, ih]

/-- Constructor-pattern encoding has the original tag and child-list shape. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "encode_pat_def"]
theorem encodePat_pcon_source (tag : Option (FlatLang.CtorId × FlatLang.TypeGroupId))
    (ps : List FlatLang.Pat) :
    encodePat (.pcon tag ps) =
      .cons (match tag with
        | none => none
        | some (id, none) => some (id, none)
        | some (id, some (_, ctors)) => some (id, some ctors)) (ps.map encodePat) := by
  cases tag with
  | none => simp [encodePat, encodePats_eq_map]
  | some pair =>
    rcases pair with ⟨id, group⟩
    cases group with
    | none => simp [encodePat, encodePats_eq_map]
    | some group => cases group; simp [encodePat, encodePats_eq_map]

end Flapjack.Compiler.Backend.FlatPattern
