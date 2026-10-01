import Flapjack.Compiler.Backend.Semantics.TargetSem.Machine
import Flapjack.Misc.BytesInMemory
import Flapjack.Misc.ShiftSeq

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

/-- Exact HOL `encoded_bytes_in_mem_def`: some encoded instruction block
    (`c.encode i`) appears in memory at `pc` after dropping a whole number of
    alignment blocks. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "encoded_bytes_in_mem_def"
  (words_as_type_indexed_bitvec)]
def encodedBytesInMemHOL {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (pc : BitVec width) (m : BitVec width → BitVec 8)
    (md : BitVec width → Prop) : Prop :=
  ∃ i : HolAsm width, ∃ k : Nat,
    k * 2 ^ c.codeAlignment < (c.encode i).length ∧
      bytesInMemoryHOL pc ((c.encode i).drop (k * 2 ^ c.codeAlignment)) m md

end Flapjack
