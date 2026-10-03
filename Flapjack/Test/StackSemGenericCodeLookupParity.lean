import Flapjack.Compiler.Backend.Semantics.StackSem.Control

/-! Original generic-register-key observations from
stackprops_ordered_code_labels_probe.out. Bool/list keys, independent word
widths and unchanged natural-register callers use the same actual definition. -/
namespace Flapjack.Test.StackSemGenericCodeLookupParity
open Flapjack StackSemControl

private def code : Spt Nat := sptFromAList [(7,41)]
private def boolRegs : HolFiniteMapExact Bool (WordLocW 1) :=
  HolFiniteMapExact.empty.updateEq (true,.loc 7 0)
private def listRegs : HolFiniteMapExact (List Nat) (WordLocW 80) :=
  HolFiniteMapExact.empty.updateEq ([1,2],.loc 7 0)

private theorem key_bool_direct :
    findCode (.inl 7 : Sum Nat Bool) (HolFiniteMapExact.empty : HolFiniteMapExact Bool (WordLocW 1)) code =
      some 41 := by decide +kernel
private theorem key_bool_indirect : findCode (.inr true) boolRegs code = some 41 := by decide +kernel
private theorem key_bool_missing : findCode (.inr false) boolRegs code = none := by decide +kernel
private theorem key_bool_nonzero :
    findCode (.inr true) (HolFiniteMapExact.empty.updateEq (true,(.loc 7 2 : WordLocW 1))) code =
      none := by decide +kernel
private theorem key_bool_word :
    findCode (.inr true) (HolFiniteMapExact.empty.updateEq (true,(.word 1 : WordLocW 1))) code =
      none := by decide +kernel
private theorem key_list_indirect : findCode (.inr [1,2]) listRegs code = some 41 := by decide +kernel
private theorem key_list_missing_code :
    findCode (.inr [1,2]) (HolFiniteMapExact.empty.updateEq ([1,2],(.loc 8 0 : WordLocW 80))) code =
      none := by decide +kernel
private theorem key_nat_legacy :
    findCode (.inr 3) (HolFiniteMapExact.empty.updateEq (3,(.loc 7 0 : WordLocW 64))) code =
      some 41 := by decide +kernel

/-- Flapjack generic-key consequence with no separate HOL theorem original.
No key equality/BEq/inhabitance instance is required by the actual operation. -/
example {width : Nat} [NeZero width] {κ α : Type}
    (key : κ) (regs : HolFiniteMapExact κ (WordLocW width)) (code : Spt α) (label : Nat)
    (h : regs.lookup key = some (.loc label 0)) :
    findCode (.inr key) regs code = sptLookup label code := by
  simp only [findCode, h]

def runChecks : IO Bool := do
  IO.println "PASS original generic StackSem code lookup keys (8 kernel observations)"
  pure true

end Flapjack.Test.StackSemGenericCodeLookupParity
