import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.NewLocal
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Unit

/-! Immediate constructor creation in the 64-bit state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Memory

/-- Adding an in-range nullary block needs no change to the concrete heap. -/
theorem memoryRel_emptyBlock64 (conf : Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (vars : List (DataSem.Value × WordLocW 64)) (tag : Nat)
    (bound : tag < 2 ^ 64 / 16) (related : memoryRel conf be next refs space store memory domain vars) :
    memoryRel conf be next refs space store memory domain
      ((.block 0 tag [], .word (BitVec.ofNat 64 (16 * tag + 2))) :: vars) := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, sizeBound, spaceBound⟩ := related
  obtain ⟨roots, inv, addresses⟩ := wordInv
  refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, sizeBound, spaceBound⟩
  refine ⟨.data (.word (blockNil tag)) :: roots, ?_, ?_⟩
  · exact consThm_empty conf (vars.map Prod.fst) refs roots heap be a sp sp1 gens limit next tag ⟨inv, bound⟩
  · apply List.Forall₂.cons
    · have mask := (blockNil_mask (width := 64) (Or.inr rfl) tag).1
      simpa [wordAddr, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_comm] using congrArg WordLocW.word mask
    · exact addresses

/-- An in-range nullary block can be installed at corresponding locals. -/
theorem stateRel64_setEmptyBlock {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs) (dest tag : Nat) (bound : tag < 2 ^ 64 / 16) :
    stateRel64 conf l1 l2 (DataSem.setVar dest (.block 0 tag []) source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) (.word (BitVec.ofNat 64 (16 * tag + 2))) target) none locs := by
  apply stateRel64_setNewLocal conf l1 l2 source target locs related
  apply memoryRel_emptyBlock64 _ _ _ _ _ _ _ _ _ tag bound
  simpa using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
