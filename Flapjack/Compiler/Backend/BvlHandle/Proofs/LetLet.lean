import Flapjack.Compiler.Backend.BvlHandle

/-! The production environment packer uses a zip with a range for the
source's indexed map. This proof connects the two formulations. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Bvl DbVars

/-- The executed packer has the original indexed-map equation, for any tree
payload type and including noncanonical trees. -/
theorem letLet_source_equation {α : Type} (envSize : Nat) (live : Spt α) (body : Exp) :
    letLet envSize live body =
      let xs := List.range envSize
      let zs := xs.filter fun n => (sptLookup n live).isSome
      let ys := zs.mapIdx fun i x => (x, i)
      let long := xs.map fun n =>
        match ys.lookup n with
        | some k => .var k
        | none => .op (.intOp (.const 0)) []
      .let (zs.map .var) (smartLet long body) := by
  simp [letLet, List.mapIdx_eq_zipIdx_map, List.zipIdx_eq_zip_range', ← List.range_eq_range']
  rfl

end Flapjack.Compiler.Backend.BvlHandle.Proofs
