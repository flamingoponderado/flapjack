import Flapjack.Compiler.Backend.Semantics.WordSem.State

/-!
# Shared WordToStack oracle fixture

The concrete free base state `base` used by the WordToStack HOL oracle rows in
`Flapjack/Test/WordToStackCallLocalRecoveryParity.lean` and
`Flapjack/Test/WordToStackMoveReconstructionParity.lean`. The HOL probes
update fields of a free state `s`; both files update the same fields of this
one instance of `s`.
-/

namespace Flapjack.Test.Fixtures.WordToStack

open Flapjack

/-- A concrete free `wordSem` state with every field at its empty/default value. -/
def base {width : Nat} [NeZero width] : WordSemStateFiniteExact width Unit Unit where
  locals := .ln
  localsSize := none
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := []
  stackLimit := 0
  stackMax := none
  stackSize := .ln
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  permute := fun _ i => i
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  handler := 0
  clock := 0
  termdep := 0
  code := .ln
  be := false
  ffi := { oracle := fun _ state _ _ => .ret state [], ffiState := (), ioEvents := [] }

end Flapjack.Test.Fixtures.WordToStack
