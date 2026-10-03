import Flapjack.Misc.BytesInMem.Imp
namespace Flapjack.Test.MiscBytesInMemImpParity
open Flapjack
example {width : Nat} [NeZero width] (values : List (BitVec 8))
    (address : BitVec width) (memory : BitVec width → BitVec 8)
    (domain excluded : BitVec width → Prop) :
    bytesInMemHOL address values memory domain excluded →
      bytesInMemoryHOL address values memory domain :=
  bytesInMem_impliesMemory values address memory domain excluded
example : bytesInMemoryHOL (255 : BitVec 8) [3,3] (fun _ => 3)
    (fun a => a = 255 ∨ a = 0) :=
  bytesInMem_impliesMemory [3,3] 255 (fun _ => 3) (fun a => a=255 ∨ a=0)
    (fun _ => False) (by cbv)
example : bytesInMemoryHOL (1 : BitVec 1) [3,3] (fun _ => 3) (fun _ => True) :=
  bytesInMem_impliesMemory [3,3] 1 (fun _ => 3) (fun _ => True)
    (fun _ => False) (by cbv)
example : bytesInMemHOL (7 : BitVec 8) [(3 : BitVec 8)] (fun _ => 3) (fun _ => True)
    (fun a => a=7) → False := by
  intro h
  exact h.2.1 rfl
example : ¬bytesInMemHOL (7 : BitVec 8) [(3 : BitVec 8)] (fun _ => 3) (fun _ => False)
    (fun _ => False) := by cbv
example : ¬bytesInMemHOL (7 : BitVec 8) [(3 : BitVec 8)] (fun _ => 4) (fun _ => True)
    (fun _ => False) := by cbv
end Flapjack.Test.MiscBytesInMemImpParity
