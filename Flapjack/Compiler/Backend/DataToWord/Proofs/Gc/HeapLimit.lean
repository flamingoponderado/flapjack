module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Limits
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Misc.GoodDimindex
import Mathlib.Tactic.NormNum

@[expose] public section

/-! Connecting the source heap limit with the collector's heap invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Flapjack-specific factoring of the heap-length equality derived inside
HOL's `state_rel_gc_gen` proof; there is no separately named HOL theorem. -/
theorem limitsInv_heapInMemoryStore_limit {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 limit next : Nat) (gens : GcCombined.GenState)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (vars : List (DataSem.Value × WordLocW width))
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stackLimit : Nat) (good : goodDimindex width)
    (limitsRel : limitsInv limits (store.lookup .heapLength) stackLimit conf.lenSize conf.hasFpOps conf.hasFpTern)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (invariant : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs vars) :
    limits.heapLimit = limit := by
  obtain ⟨_, _, _, limitsWord, limitsBound, _, _⟩ := limitsRel
  obtain ⟨_, heapBound, _, _, _, _, _, curr, other, _, _, _, _, _, _, _, heapWord, _⟩ := heapMem
  obtain ⟨roots, abstractInv, _⟩ := invariant
  have heapLen : heapLength heap = limit := abstractInv.2.1.1
  rw [heapLen] at heapBound
  have wordEq : BitVec.ofNat width (width / 8) * BitVec.ofNat width limits.heapLimit =
      BitVec.ofNat width (width / 8) * BitVec.ofNat width limit := by
    rw [heapWord] at limitsWord
    simpa [StackRemove.bytesInWord] using limitsWord.symm
  have natEq := congrArg BitVec.toNat wordEq
  rcases good with rfl | rfl <;>
    norm_num [BitVec.toNat_ofNat] at limitsBound heapBound ⊢
  all_goals simp only [← BitVec.ofNat_mul, BitVec.toNat_ofNat] at natEq
  all_goals rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at natEq
  all_goals omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
