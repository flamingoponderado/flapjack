import Flapjack.Test.CrepGlobalShapeParity
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedDecs

/-!
Direct Lean counterparts to `scripts/hol-probes/globals_lookup_probe.out`,
which evaluates the original `pan_to_crepProof$globals_lookup_def` for one
populated global slot, a missing lookup, and a two-word `RStruct`.
-/

namespace Flapjack.Test.PanToCrepGlobalsLookupParity

open Flapjack
open Flapjack.Test.CrepGlobalShapeParity

def populatedGlobalsState : CrepRuntimeState Nat Unit :=
  { globalState with globals :=
      updateCrepRuntimeGlobal (fun _ => none) (0 : BitVec 5) (.word 7) }

def twoPopulatedGlobalsState : CrepRuntimeState Nat Unit :=
  { globalState with globals := (
      updateCrepRuntimeGlobal
        (updateCrepRuntimeGlobal (fun _ => none) (0 : BitVec 5) (.word 7))
        (1 : BitVec 5) (.word 8)) }

/- HOL globals_lookup_probe: lookup_success=SOME [Word 7w]. -/
#guard globalsLookup populatedGlobalsState (.word 11) == some [.word 7]

/- HOL globals_lookup_probe: lookup_missing=NONE. -/
#guard (globalsLookup globalState (.word 11)).isNone

/- HOL globals_lookup_probe: lookup_struct=SOME [Word 7w; Word 8w]. -/
#guard globalsLookup twoPopulatedGlobalsState (.rStruct [.word 3, .word 4]) ==
  some [.word 7, .word 8]

/- The checks above exercise the production analogue. These three checks
   exercise the tagged exact HOL carrier against the same direct HOL EVAL rows. -/
private def exactGlobalsState : CrepSemHOLState 8 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
    [((0 : BitVec 5), .word (BitVec.ofNat 8 7)),
     ((1 : BitVec 5), .word (BitVec.ofNat 8 8))]
  code := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 0
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 0

/- HOL globals_lookup_probe: lookup_success=SOME [Word 7w]. -/
#guard globalsLookupHOL exactGlobalsState (.val (.word (BitVec.ofNat 8 7))) ==
  some [.word (BitVec.ofNat 8 7)]

/- HOL globals_lookup_probe: lookup_missing=NONE. -/
#guard (globalsLookupHOL { exactGlobalsState with globals := HolFiniteMapExact.empty }
  (.val (.word (BitVec.ofNat 8 7)))).isNone

/- HOL globals_lookup_probe: lookup_struct=SOME [Word 7w; Word 8w]. -/
#guard globalsLookupHOL exactGlobalsState
  (.rStruct [.val (.word (BitVec.ofNat 8 3)), .val (.word (BitVec.ofNat 8 4))]) ==
  some [.word (BitVec.ofNat 8 7), .word (BitVec.ofNat 8 8)]

end Flapjack.Test.PanToCrepGlobalsLookupParity
