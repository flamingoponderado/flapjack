import Flapjack.Compiler.Backend.StackRemove.Proofs.WordStore

namespace Flapjack.Compiler.Backend.StackRemove.WordStoreLaws
open Flapjack Flapjack.Compiler.Backend.StackRemove

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Updating CurrHeap leaves the full store heap assertion unchanged because
CurrHeap is not among the original ordered store slots. Address and stored-word
dimensions remain independent, as in HOL; arbitrary Word or Loc updates pass
through the actual native finite-map carrier. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordStoreCurrHeap {addressWidth : Nat} {valueWidth : Nat}
    [NeZero addressWidth] [NeZero valueWidth] {C F : Type}
    (base : BitVec addressWidth) (state : StackSemStateFiniteExact valueWidth C F)
    (value : WordLocW valueWidth) :
    wordStoreHOL base (state.store.updateEq (.currHeap, value)) = wordStoreHOL base state.store := by
  simp [wordStoreHOL, storeList, StackSemRegisterTransfers.storeOfSyntax,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end Flapjack.Compiler.Backend.StackRemove.WordStoreLaws
