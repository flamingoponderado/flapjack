import Flapjack.Pancake.Proofs.PanGlobals.MemStores
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsDisjoint

namespace Flapjack.PanGlobalsInitGlobalsRanges
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Flapjack-specific factoring of the initializer cons arithmetic in HOL
2182-2235. Updating globals_size by the head allocation leaves the recursive
tail's free-range base equal to the original combined free-range base.
No independently named HOL declaration or non-wrapping premise is used. -/
theorem recursiveFreeBase {width : Nat} (top globals : BitVec width)
    (head tail : Nat) :
    top - panBytesInWord width * BitVec.ofNat width (head + tail) - globals =
      top - panBytesInWord width * BitVec.ofNat width tail -
        (globals + panBytesInWord width * BitVec.ofNat width head) := by
  rw [BitVec.ofNat_add, BitVec.mul_add, BitVec.sub_sub, BitVec.sub_sub]
  congr 1
  ac_rfl

/-- The first initializer occupies the suffix after the recursive tail's
range. This modular equation needs no disjointness bound. -/
theorem headAllocationBase {width : Nat} (top globals : BitVec width)
    (head tail : Nat) :
    (top - panBytesInWord width * BitVec.ofNat width (head + tail) - globals) +
        panBytesInWord width * BitVec.ofNat width tail =
      top - (globals + panBytesInWord width * BitVec.ofNat width head) := by
  rw [recursiveFreeBase, BitVec.sub_sub]
  have hswap :
      panBytesInWord width * BitVec.ofNat width tail +
          (globals + panBytesInWord width * BitVec.ofNat width head) =
        (globals + panBytesInWord width * BitVec.ofNat width head) +
          panBytesInWord width * BitVec.ofNat width tail := by ac_rfl
  rw [hswap, ← BitVec.sub_sub, BitVec.sub_add_cancel]

/-- Source-derived initializer allocation certificate. Prefix/suffix
containment comes from accepted addresses_add; disjointness uses exactly the
original good_dimindex and combined-size bound. This is composition
infrastructure, not a separate HOL theorem or target-evaluation assumption. -/
theorem allocationPartition {width : Nat} [NeZero width]
    (top globals : BitVec width) (head tail : Nat)
    (hwidth : goodDimindex width)
    (hbound : (panBytesInWord width).toNat * (head + tail) < 2 ^ width) :
    let freeBase := top - panBytesInWord width * BitVec.ofNat width (head + tail) - globals
    let headBase := top - (globals + panBytesInWord width * BitVec.ofNat width head)
    (∀ address, addresses freeBase tail address → addresses freeBase (head + tail) address) ∧
    (∀ address, addresses headBase head address → addresses freeBase (head + tail) address) ∧
    (∀ address, addresses freeBase tail address → ¬ addresses headBase head address) := by
  dsimp only
  let freeBase := top - panBytesInWord width * BitVec.ofNat width (head + tail) - globals
  let headBase := top - (globals + panBytesInWord width * BitVec.ofNat width head)
  have hbase : freeBase + panBytesInWord width * BitVec.ofNat width tail = headBase :=
    headAllocationBase top globals head tail
  have hsplit := PanGlobalsMemStores.addresses_add tail head freeBase
  have hdisjoint := PanGlobalsInitGlobalsDisjoint.disjointAddressesHOL
    freeBase headBase tail head ⟨hbase, hwidth, by simpa [Nat.add_comm] using hbound⟩
  refine ⟨?_, ?_, hdisjoint⟩
  · intro address h
    simpa only [Nat.add_comm] using (hsplit address).mpr (Or.inl h)
  · intro address h
    change addresses headBase head address at h
    rw [← hbase] at h
    have h' : addresses (freeBase + BitVec.ofNat width (width / 8) * BitVec.ofNat width tail)
        head address := by simpa only [panBytesInWord] using h
    simpa only [Nat.add_comm] using (hsplit address).mpr (Or.inr h')

/-- The recursive initializer inherits the original target-domain coverage
and source-domain disjointness after the compiler advances globals_size.
The new head block is also disjoint from the recursive free range. These are
the original induction-premise obligations, with no store or run premise. -/
theorem recursiveFreeRangePremises {width : Nat} [NeZero width]
    (top globals : BitVec width) (head tail : Nat)
    (sourceDomain targetDomain : BitVec width → Prop)
    (hwidth : goodDimindex width)
    (hbound : (panBytesInWord width).toNat * (head + tail) < 2 ^ width)
    (hcoverage : ∀ address,
      addresses (top - panBytesInWord width * BitVec.ofNat width (head + tail) - globals)
        (head + tail) address → targetDomain address)
    (hexcluded : ∀ address, sourceDomain address →
      ¬ addresses (top - panBytesInWord width * BitVec.ofNat width (head + tail) - globals)
        (head + tail) address) :
    let recursiveBase := top - panBytesInWord width * BitVec.ofNat width tail -
      (globals + panBytesInWord width * BitVec.ofNat width head)
    (∀ address, addresses recursiveBase tail address → targetDomain address) ∧
    (∀ address, sourceDomain address → ¬ addresses recursiveBase tail address) ∧
    (∀ address, addresses recursiveBase tail address →
      ¬ addresses (top - (globals + panBytesInWord width * BitVec.ofNat width head))
        head address) := by
  dsimp only
  rw [← recursiveFreeBase top globals head tail]
  obtain ⟨hprefix, _, hdisjoint⟩ := allocationPartition top globals head tail hwidth hbound
  exact ⟨fun address h => hcoverage address (hprefix address h),
    fun address hsource htail => hexcluded address hsource (hprefix address htail), hdisjoint⟩

end Flapjack.PanGlobalsInitGlobalsRanges
