import Flapjack.Compiler.Backend.LabToTarget.Positions

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Misc

/-- Original two-level tree lookup is polymorphic in its value carrier.
Missing either level returns NONE; no default position is inserted. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_lookup_def"]
def labLookup {α : Type} (k1 k2 : Nat) (labs : Spt (Spt α)) : Option α :=
  match sptLookup k1 labs with
  | none => none
  | some f => sptLookup k2 f

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_lookup_IMP"]
theorem labLookup_implies_findPos (l1 l2 : Nat) (labs : Spt (Spt Nat)) (x : Nat) :
    labLookup l1 l2 labs = some x → findPos (.lab l1 l2) labs = x := by
  unfold labLookup findPos lookupAny
  cases ho : sptLookup l1 labs <;> simp [ho]
  rename_i inner
  cases hi : sptLookup l2 inner <;> simp

end Flapjack.Compiler.Backend.LabToTarget
