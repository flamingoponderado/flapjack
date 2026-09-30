import Flapjack.Pancake.Proofs.PanGlobals.ByteStore

/-!
# pan_globals `state_rel_write_bytearray`

Counterpart of `cakeml/pancake/proofs/pan_globalsProofScript.sml:1571-1593`
(bead `flapjack-pxn.18.5.2.35`): parallel exact `write_bytearray` updates of the
same byte list at the same address preserve `state_rel`, given a successful
source byte-array read of that region.  Uses the exact `word8` carriers
`readBytearrayWordHOL`, `panMemLoadByteWord8HOL` and
`panWriteBytearrayWord8HOL` and the closed `state_rel_read_bytearray` /
`state_rel_mem_store_byte` prerequisites.
-/

namespace Flapjack.PanGlobalsWriteBytearray
open Flapjack

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

set_option maxHeartbeats 1600000 in
private theorem writeBytearray_rel {width : Nat} [NeZero width] {σ : Type}
    (flag : Bool) (context : PanGlobalsContextExact width) :
    ∀ (bytes : List (BitVec 8)) (source target : PanSemStateFiniteExact width σ)
      (address : BitVec width) (newBytes : List (BitVec 8)),
      panGlobalsStateRelHOLExact flag context source target →
      readBytearrayWordHOL address bytes.length
        (@panMemLoadByteWord8HOL width _ source.memory source.memaddrs
          (fun a => Classical.propDecidable (source.memaddrs a)) source.be) = some newBytes →
      panGlobalsStateRelHOLExact flag context
        { source with memory :=
            (@panWriteBytearrayWord8HOL width _ address bytes source.memory
              source.memaddrs (fun a => Classical.propDecidable (source.memaddrs a))
              source.be) }
        { target with memory :=
            (@panWriteBytearrayWord8HOL width _ address bytes target.memory
              target.memaddrs (fun a => Classical.propDecidable (target.memaddrs a))
              target.be) } := by
  classical
  intro bytes
  induction bytes with
  | nil =>
      intro source target address newBytes hrel hread
      change panGlobalsStateRelHOLExact flag context
        { source with memory := source.memory } { target with memory := target.memory }
      exact hrel
  | cons b bs ih =>
      intro source target address newBytes hrel hread
      have hread' := hread
      change (Option.bind
          (@panMemLoadByteWord8HOL width _ source.memory source.memaddrs
            (fun a => Classical.propDecidable (source.memaddrs a)) source.be address)
          (fun byte => Option.bind
            (@readBytearrayWordHOL width 8 _ _ (address + 1) bs.length
              (@panMemLoadByteWord8HOL width _ source.memory source.memaddrs
                (fun a => Classical.propDecidable (source.memaddrs a)) source.be))
            (fun rest => some (byte :: rest)))) = some newBytes at hread'
      cases hb : @panMemLoadByteWord8HOL width _ source.memory source.memaddrs
          (fun a => Classical.propDecidable (source.memaddrs a)) source.be address with
      | none => simp [hb] at hread'
      | some byte =>
          rw [hb] at hread'
          cases hr : readBytearrayWordHOL (address + 1) bs.length
              (@panMemLoadByteWord8HOL width _ source.memory source.memaddrs
                (fun a => Classical.propDecidable (source.memaddrs a)) source.be) with
          | none => rw [hr] at hread'; simp at hread'
          | some rest =>
              rw [hr] at hread'
              have hdom : source.memaddrs (panByteAlignHOL address) := by
                cases hm : source.memory (panByteAlignHOL address) with
                | word cell =>
                    by_cases hd : source.memaddrs (panByteAlignHOL address)
                    · exact hd
                    · simp [panMemLoadByteWord8HOL, hd] at hb
              generalize hsW :
                @panWriteBytearrayWord8HOL width _ (address + 1) bs source.memory
                  source.memaddrs (fun a => Classical.propDecidable (source.memaddrs a))
                  source.be = sW
              generalize htW :
                @panWriteBytearrayWord8HOL width _ (address + 1) bs target.memory
                  target.memaddrs (fun a => Classical.propDecidable (target.memaddrs a))
                  target.be = tW
              have hrelTail : panGlobalsStateRelHOLExact flag context
                  { source with memory := sW } { target with memory := tW } := by
                rw [← hsW, ← htW]
                exact ih source target (address + 1) rest hrel hr
              cases hm2 : sW (panByteAlignHOL address) with
              | word cell2 =>
                  have hstoreSome :
                      @panMemStoreByteWord8HOL width _ sW source.memaddrs
                        (fun a => Classical.propDecidable (source.memaddrs a))
                        source.be address b =
                        some (fun current => if current = panByteAlignHOL address then
                          HolWordLab.word (panSetByteHOL address (BitVec.ofNat width b.toNat) cell2 source.be)
                          else sW current) := by
                    unfold panMemStoreByteWord8HOL
                    dsimp only
                    rw [hm2, if_pos hdom]
                  obtain ⟨u_t, hstoreT, hrelUpd⟩ :=
                    Flapjack.PanGlobalsByteStore.stateRelMemStoreByte flag context
                      { source with memory := sW } { target with memory := tW } address b
                      (fun current => if current = panByteAlignHOL address then
                        HolWordLab.word (panSetByteHOL address (BitVec.ofNat width b.toNat) cell2 source.be)
                        else sW current)
                      ⟨hrelTail, hstoreSome⟩
                  rw [panWriteBytearrayWord8HOL, panWriteBytearrayWord8HOL]
                  rw [hsW, htW]
                  rw [hstoreSome, hstoreT]
                  dsimp only
                  exact hrelUpd

/-- Original HOL1571-1593 byte-array write simulation: related source/target
    states and a successful source read of the written region imply the target
    write also succeeds and the written states stay related. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_write_bytearray"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelWriteBytearray {width : Nat} {σ : Type} [NeZero width]
    (flag : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (address : BitVec width) (bytes newBytes : List (BitVec 8)) :
    panGlobalsStateRelHOLExact flag context source target ∧
      readBytearrayWordHOL address bytes.length
        (@panMemLoadByteWord8HOL width _ source.memory source.memaddrs
          (fun a => Classical.propDecidable (source.memaddrs a)) source.be) = some newBytes →
    panGlobalsStateRelHOLExact flag context
      { source with memory :=
          (@panWriteBytearrayWord8HOL width _ address bytes source.memory
            source.memaddrs (fun a => Classical.propDecidable (source.memaddrs a))
            source.be) }
      { target with memory :=
          (@panWriteBytearrayWord8HOL width _ address bytes target.memory
            target.memaddrs (fun a => Classical.propDecidable (target.memaddrs a))
            target.be) } := by
  intro ⟨hrel, hread⟩
  exact writeBytearray_rel flag context bytes source target address newBytes hrel hread

end Flapjack.PanGlobalsWriteBytearray
