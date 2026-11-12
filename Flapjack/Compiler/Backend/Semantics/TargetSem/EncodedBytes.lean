module

public import Flapjack.Compiler.Backend.Semantics.TargetSem.Machine
public import Flapjack.Misc.BytesInMemory
public import Flapjack.Misc.ShiftSeq

@[expose] public section

/-!
Exact targetSem prerequisites that validate encoded machine code against the
machine memory: `apply_oracle_def` (`targetSemScript.sml:46-48`) and
`encoded_bytes_in_mem_def` (`:52-57`).

`bytes_in_memory` itself is a miscScript declaration and lives in its
miscScript counterpart `Flapjack.Misc.BytesInMemory`.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `apply_oracle_def`: advance an oracle by one step and return the
    current answer together with the shifted oracle. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "apply_oracle_def"]
def applyOracleHOL {α β : Type} (oracle : Nat → α → β) (x : α) :
    β × (Nat → α → β) :=
  (oracle 0 x, holShiftSeq 1 oracle)

/-- HOL `encoded_bytes_in_mem_def`: some encoded instruction block
    (`c.encode i`) appears in memory at `pc` after dropping a whole number of
    alignment blocks.

    Tag withdrawn (task 149): the typed capture
    `encoded_bytes_in_mem_def_typed` (`target_sem_typed_probe.out`) gives
    `c : α asm_config` and `pc : β word`, so HOL's instruction type `α` is
    independent of the word dimension. Lean's `AsmConfigExact` fixes the
    instruction type at `HolAsm width` (`encode : HolAsm width → List (BitVec 8)`),
    so this is the `α = HolAsm width` instance, not an exact port. A faithful
    port needs an asm-config carrier generic in its instruction type. -/
def encodedBytesInMemHOL {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (pc : BitVec width) (m : BitVec width → BitVec 8)
    (md : BitVec width → Prop) : Prop :=
  ∃ i : HolAsm width, ∃ k : Nat,
    k * 2 ^ c.codeAlignment < (c.encode i).length ∧
      bytesInMemoryHOL pc ((c.encode i).drop (k * 2 ^ c.codeAlignment)) m md

end Flapjack
