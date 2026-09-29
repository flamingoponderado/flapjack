import Flapjack.Pancake.Semantics.LoopSem

/-!
# Width-generic memory helper parity

The `memLoadHOL`/`memStoreHOL` split-argument helpers below are
FLAPJACK-SPECIFIC convenience functions; they are not the whole-state HOL
`loopSem.mem_load`/`mem_store` definitions. The exact tagged definitions are
`LoopSemStateFiniteExact.memLoad`/`memStore` in
`Flapjack/Pancake/Semantics/LoopSemStateExact.lean`. Their direct HOL-EVAL
rows from `scripts/hol-probes/loop_sem_mem_load_probe.out` and
`loop_sem_mem_store_probe.out` are checked over the same total-state carrier
in `Flapjack/Test/LoopSemEvalExactParity.lean`.

`memLoad32HOL`/`memStore32HOL` are the exact width-generic ports of
`cakeml/compiler/backend/semantics/wordSemScript.sml:70-81` and `:84-97`
(aligned-2 four-byte word load/store reassembled with the polymorphic
`get_byte`/`set_byte` codec).
-/

namespace Flapjack.Test.LoopMemExactParity

open Flapjack

abbrev Word := RiscV.Word 64

def totalMemory : Word → LoopValue Word :=
  fun address => if address = 3 then .word 7 else .loc 0 0

abbrev totalDomain : Word → Prop :=
  fun address => address = 3

def loadHit : Bool := memLoadHOL totalMemory totalDomain (3 : Word) = some (.word 7)
def loadMiss : Bool := memLoadHOL totalMemory totalDomain (4 : Word) = none

def storeHit : Bool :=
  (memStoreHOL totalMemory totalDomain (3 : Word) (.word 9)).map (fun memory => memory 3)
    = some (.word 9)
def storeMiss : Bool := memStoreHOL totalMemory totalDomain (4 : Word) (.word 9) = none
def storeKeepsOther : Bool :=
  (memStoreHOL totalMemory totalDomain (3 : Word) (.word 9)).map (fun memory => memory 4)
    = some (.loc 0 0)

#guard loadHit
#guard loadMiss
#guard storeHit
#guard storeMiss
#guard storeKeepsOther

def memory32 : Word → LoopValue Word :=
  fun address => if address = 0 then .word 0x11223344 else .loc 0 0

abbrev domain32 : Word → Prop :=
  fun address => address = 0

def load32Hit : Bool :=
  memLoad32HOL memory32 domain32 false (0 : Word) = some (0x11223344 : RiscV.Word 32)
def load32Misaligned : Bool :=
  memLoad32HOL memory32 domain32 false (2 : Word) = none
def load32Loc : Bool :=
  memLoad32HOL memory32 domain32 false (8 : Word) = none
def store32Hit : Bool :=
  (memStore32HOL memory32 domain32 false (0 : Word) (0xAABBCCDD : RiscV.Word 32)).map
      (fun memory => memory 0)
    = some (.word 0xAABBCCDD)
def store32Misaligned : Bool :=
  memStore32HOL memory32 domain32 false (2 : Word) (0xAABBCCDD : RiscV.Word 32) = none

#guard load32Hit
#guard load32Misaligned
#guard load32Loc
#guard store32Hit
#guard store32Misaligned

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop mem_load exact hit reads in-domain word", loadHit),
      ("Loop mem_load exact miss rejects out-of-domain address", loadMiss),
      ("Loop mem_store exact hit updates the addressed cell", storeHit),
      ("Loop mem_store exact miss rejects out-of-domain address", storeMiss),
      ("Loop mem_store exact leaves other cells unchanged", storeKeepsOther),
      ("Loop mem_load_32 exact reads aligned four bytes", load32Hit),
      ("Loop mem_load_32 exact rejects misaligned address", load32Misaligned),
      ("Loop mem_load_32 exact rejects Loc cell", load32Loc),
      ("Loop mem_store_32 exact writes aligned four bytes", store32Hit),
      ("Loop mem_store_32 exact rejects misaligned address", store32Misaligned) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopMemExactParity
