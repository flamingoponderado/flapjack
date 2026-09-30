import Flapjack.Pancake.Proofs.PanGlobals.MemStores
import Flapjack.Pancake.Proofs.PanGlobals.ReadBytearray

namespace Flapjack.PanGlobalsByteStore
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Flapjack-only update support with an arbitrary locals flag. Unlike HOL's
state_rel_memory_update, this helper retains the input flag, so it is untagged.
Global loads are preserved using the accepted singleton mem_stores theorem. -/
private theorem stateRel_update {width : Nat} {σ : Type} [NeZero width]
    (flag : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (address : BitVec width) (value : HolWordLab width)
    (hrel : panGlobalsStateRelHOLExact flag context source target)
    (hdomain : source.memaddrs address) :
    panGlobalsStateRelHOLExact flag context
      {source with memory := fun a => if a = address then value else source.memory a}
      {target with memory := fun a => if a = address then value else target.memory a} := by
  classical
  unfold panGlobalsStateRelHOLExact at hrel ⊢
  rcases hrel with ⟨htop, hlocals, hbase, hbe, heshapes, hclock, hsourceStructs,
    htargetStructs, hglobals, hwf, hsub, hshared, hmemory, hffi, hcode, hdisjoint,
    htopOutside, haligned, hwidth⟩
  refine ⟨htop, hlocals, hbase, hbe, heshapes, hclock, hsourceStructs,
    htargetStructs, ?_, hwf, hsub, hshared, ?_, hffi, hcode, hdisjoint,
    htopOutside, haligned, hwidth⟩
  · intro name global hlookup
    obtain ⟨offset, hlookupContext, hshape, hload, hseparate, hoffset⟩ :=
      hglobals name global hlookup
    refine ⟨offset, hlookupContext, hshape, ?_, hseparate, hoffset⟩
    have hstore : panMemStoresHOL address [value] target.memaddrs target.memory =
        some (fun a => if a = address then value else target.memory a) := by
      simp [panMemStoresHOL, panMemStoreHOL, hsub address hdomain]
    have hblocks : ∀ x, addresses (target.topAddr - offset)
        (sizeOfShapeHOL (shapeOfHOLExact global)) x → ¬ addresses address 1 x := by
      intro x hx hsingle
      have heq : x = address := by simpa [addresses] using hsingle
      subst x
      exact hseparate address hdomain hx
    rw [PanGlobalsMemStores.memStoresLoadDisjointHOL.1
      (shapeOfHOLExact global) address [value] target.memaddrs target.memory
      (fun a => if a = address then value else target.memory a) []
      (target.topAddr - offset) ⟨hstore, rfl, hshape, hblocks⟩]
    exact hload
  · intro a ha
    dsimp only
    split <;> simp_all

/-- Canonical state roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad context.toBroad = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Original HOL1548-1562 byte-store simulation, with the arbitrary locals
flag retained and the target memory derived from source success. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_mem_store_byte"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelMemStoreByte {width : Nat} {σ : Type} [NeZero width]
    (flag : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (address : BitVec width) (byte : BitVec 8)
    (memory : BitVec width → HolWordLab width) :
    panGlobalsStateRelHOLExact flag context source target ∧
      @panMemStoreByteWord8HOL width _ source.memory source.memaddrs
        (fun a => Classical.propDecidable (source.memaddrs a)) source.be address byte = some memory →
    ∃ targetMemory,
      @panMemStoreByteWord8HOL width _ target.memory target.memaddrs
        (fun a => Classical.propDecidable (target.memaddrs a)) target.be address byte = some targetMemory ∧
      panGlobalsStateRelHOLExact flag context
        {source with memory := memory} {target with memory := targetMemory} := by
  classical
  intro ⟨hrel, hstore⟩
  have hbe := hrel.2.2.2.1
  have hsub := hrel.2.2.2.2.2.2.2.2.2.2.1
  have hmem := hrel.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hm : source.memory (panByteAlignHOL address) with
  | word cell =>
      by_cases hd : source.memaddrs (panByteAlignHOL address)
      · have htargetCell := hmem _ hd
        simp only [panMemStoreByteWord8HOL, hm, if_pos hd, Option.some.injEq] at hstore
        subst memory
        refine ⟨(fun a => if a = panByteAlignHOL address then
          .word (panSetByteHOL address (BitVec.ofNat width byte.toNat) cell source.be)
          else target.memory a), ?_, ?_⟩
        · simp [panMemStoreByteWord8HOL, ← htargetCell, hm, hsub _ hd, ← hbe]
        · exact stateRel_update flag context source target (panByteAlignHOL address)
            (.word (panSetByteHOL address (BitVec.ofNat width byte.toNat) cell source.be)) hrel hd
      · simp [panMemStoreByteWord8HOL, hd] at hstore

end Flapjack.PanGlobalsByteStore
