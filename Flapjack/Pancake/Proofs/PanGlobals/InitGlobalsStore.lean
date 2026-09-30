import Flapjack.Pancake.Proofs.PanGlobals.MemoryLookup

namespace Flapjack.PanGlobalsInitGlobalsStore

open Flapjack
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Initializer-cons memory certificate for the source-memory conjunct at
`pan_globalsProofScript.sml:2285-2300`. The head store footprint lies in the
reserved free region, which is covered by the target domain and disjoint
from the source domain. Consequently the store succeeds and preserves the
old source/target memory agreement. Modular addresses may wrap.

This composition of `mem_stores_addrs_IS_SOME` and `mem_stores_lookup` is
Flapjack infrastructure, untagged because HOL has no separate declaration
for this proof step. It does not establish the full initializer state
relation or recursive initialization theorem. -/
theorem initGlobalStorePreservesSourceMemory {width : Nat} [NeZero width]
    (address : BitVec width) (values : List (HolWordLab width))
    (sourceDomain targetDomain freeRegion : BitVec width → Prop)
    (sourceMemory targetMemory : BitVec width → HolWordLab width)
    (hfootprint : ∀ slot, addresses address values.length slot → freeRegion slot)
    (hcoverage : ∀ slot, freeRegion slot → targetDomain slot)
    (hdisjoint : ∀ slot, sourceDomain slot → ¬ freeRegion slot)
    (hagreement : ∀ slot, sourceDomain slot → sourceMemory slot = targetMemory slot) :
    letI : DecidablePred targetDomain := fun slot => Classical.propDecidable (targetDomain slot)
    ∃ updatedMemory,
      panMemStoresHOL address values targetDomain targetMemory = some updatedMemory ∧
      ∀ slot, sourceDomain slot → sourceMemory slot = updatedMemory slot := by
  classical
  obtain ⟨updatedMemory, hstore⟩ :=
    PanGlobalsInitGlobalsMemory.memStoresAddrsIsSomeHOL address values targetDomain targetMemory
      (fun slot hin => hcoverage slot (hfootprint slot hin))
  refine ⟨updatedMemory, hstore, ?_⟩
  intro slot hsource
  have hout : ¬ addresses address values.length slot :=
    fun hin => hdisjoint slot hsource (hfootprint slot hin)
  have hlookup := PanGlobalsMemoryLookup.memStoresLookupHOL address values targetDomain
    targetMemory updatedMemory slot ⟨hstore, hout⟩
  exact (hagreement slot hsource).trans hlookup.symm

end Flapjack.PanGlobalsInitGlobalsStore
