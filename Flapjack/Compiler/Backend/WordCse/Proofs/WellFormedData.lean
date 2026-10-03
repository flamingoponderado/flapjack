import Flapjack.Compiler.Backend.WordCse.Knowledge
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.InstructionKeys
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.WordCse.Proofs.InNamesSet
import Flapjack.Misc.BalancedMap.Invariants

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack

/-- Full original eleven-conjunct knowledge invariant. The HOL type dimension
occurs in the internally quantified arithmetic instruction and load offset,
not in the knowledge carrier. The word qualifier records precisely those
positive-width carriers; no dummy word argument, successful evaluation,
flatness or output relation is added. Sparse domains, ordered store-list
distinctness and both complete native tree invariants are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_def"
  (words_as_type_indexed_bitvec)]
def wfData (width : Nat) [NeZero width] (data : Knowledge) : Prop :=
  (∀ (register value : Nat),
    sptLookup register data.toCanonical = some value →
      sptLookup value data.toCanonical = some value ∧
      register % 2 = 1 ∧ value % 2 = 1) ∧
  (∀ (register value : Nat),
    sptLookup register data.toLatest = some value →
      sptDomain data.toCanonical register ∧ sptDomain data.toCanonical value) ∧
  (∀ (key : List Nat) (value : Nat),
    Misc.BalancedMap.lookup listCmp key data.instrsMem = some value →
      sptLookup value data.toCanonical = some value) ∧
  (∀ (operation : Compiler.Encoders.Asm.HolArith width) (value : Nat),
    Misc.BalancedMap.lookup listCmp (instToNumList (.arith operation)) data.instrsMem = some value →
      inNamesSet operation data.toCanonical ∧ canMemArith operation = true) ∧
  (∀ (operator : BinOp) (source value : Nat),
    Misc.BalancedMap.lookup listCmp (opCurrHeapToNumList operator source) data.instrsMem = some value →
      sptLookup source data.toCanonical = some source) ∧
  (∀ (store : WordStoreHOL) (value : Nat),
    data.getsMem.lookup store = some value →
      sptLookup value data.toCanonical = some value) ∧
  (data.getsMem.map Prod.fst).Nodup ∧
  Misc.BalancedMap.invariant listCmp data.instrsMem ∧
  (∀ (key : List Nat) (value : Nat),
    Misc.BalancedMap.lookup listCmp key data.loadsMem = some value →
      sptLookup value data.toCanonical = some value) ∧
  (∀ (operator : Compiler.Encoders.Asm.HolMemop) (address : Nat)
      (offset : BitVec width) (value : Nat),
    Misc.BalancedMap.lookup listCmp (loadToNumList operator address offset) data.loadsMem = some value →
      sptLookup address data.toCanonical = some address) ∧
  Misc.BalancedMap.invariant listCmp data.loadsMem

end Flapjack.Compiler.Backend.WordCse
