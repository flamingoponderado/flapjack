import Flapjack.Compiler.Backend.WordCse.Knowledge

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack

/-- Original odd-register tracking, updating only to_canonical when the
register is not already tracked. Other four knowledge fields are retained. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "register_read_def"]
def registerRead (data : Knowledge) (register : Nat) : Knowledge :=
  if register % 2 != 0 && keepData data.toCanonical register then
    {data with toCanonical := sptInsert register register data.toCanonical}
  else data

@[hol "cakeml/compiler/backend/word_cseScript.sml" "register_reads_def"]
def registerReads (data : Knowledge) : List Nat → Knowledge
  | [] => data
  | register :: registers => registerReads (registerRead data register) registers

/-- Original lookup_any with the register itself as the default. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "canonicalRegs_def"]
def canonicalRegs (data : Knowledge) (register : Nat) : Nat :=
  (sptLookup register data.toCanonical).getD register

@[hol "cakeml/compiler/backend/word_cseScript.sml" "canonicalRegs'_def"]
def canonicalRegs' (avoid : Nat) (data : Knowledge) (register : Nat) : Nat :=
  let canonical := canonicalRegs data register
  if canonical = avoid then register else canonical

@[hol "cakeml/compiler/backend/word_cseScript.sml" "canonicalMultRegs_def"]
def canonicalMultRegs (data : Knowledge) (registers : List Nat) : List Nat :=
  registers.map (canonicalRegs data)

/-- Literal tail-first insertion: the head binding is inserted last and wins
on repeated keys, preserving the original arbitrary sparse-tree input. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "map_insert_def"]
def mapInsert : List (Nat × Nat) → Spt Nat → Spt Nat
  | [], map => map
  | (key, value) :: entries, map => sptInsert key value (mapInsert entries map)

end Flapjack.Compiler.Backend.WordCse
