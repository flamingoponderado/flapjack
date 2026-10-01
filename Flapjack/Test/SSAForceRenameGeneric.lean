import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMoveFrames

/-! Regression cases for the arbitrary HOL payload of force_rename.
These are Flapjack fixtures, not additional HOL theorem ports. -/
namespace Flapjack.Test.SSAForceRenameGeneric
open Flapjack Flapjack.Compiler.Backend.WordAlloc

example : sptLookup 3 (forceRename [(3, false), (3, true)] (.ln : Spt Bool)) =
    some true := by decide +kernel

example : sptLookup 7 (forceRename [(3, false)] (sptFromAList [(7, true)])) =
    some true := by decide +kernel

example (x : Nat) (ls : List (Nat × Bool)) (ssa : Spt Bool) :
    sptLookup x (forceRename ls.reverse ssa) =
      match Flapjack.holAlookup ls x with
      | none => sptLookup x ssa
      | some y => some y := by
  have h := lookupForceRenameAux x ls ssa
  cases hr : holAlookup ls x <;> simpa [hr] using h

example (x : Nat) (ls : List (Nat × Unit)) (ssa : Spt Unit) :
    sptLookup x (forceRename ls ssa) =
      match Flapjack.holAlookup ls.reverse x with
      | none => sptLookup x ssa
      | some y => some y := by
  have h := lookupForceRename x ls ssa
  cases hr : holAlookup ls.reverse x <;> simpa [hr] using h

example (ls : List (Nat × Bool)) (ssa : Spt Bool) :
    sptDomain (forceRename ls ssa) =
      fun x => sptDomain ssa x ∨ x ∈ ls.map Prod.fst := domainForceRename ls ssa

end Flapjack.Test.SSAForceRenameGeneric
