import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact
import Flapjack.Pancake.Semantics.LoopSem

namespace Flapjack.PanGlobalsReadBytearray
open Flapjack

/-- Flapjack-only successful-byte-load monotonicity infrastructure. It derives
agreement at the aligned address from domain inclusion and memory agreement;
no target load is assumed and there is no separate HOL declaration. -/
private theorem byteLoad_mono {width : Nat} [NeZero width]
    (sourceMemory targetMemory : BitVec width → HolWordLab width)
    (sourceDomain targetDomain : BitVec width → Prop)
    [DecidablePred sourceDomain] [DecidablePred targetDomain]
    (be : Bool) (address : BitVec width) (byte : BitVec 8)
    (hsub : ∀ a, sourceDomain a → targetDomain a)
    (hmem : ∀ a, sourceDomain a → sourceMemory a = targetMemory a)
    (h : panMemLoadByteWord8HOL sourceMemory sourceDomain be address = some byte) :
    panMemLoadByteWord8HOL targetMemory targetDomain be address = some byte := by
  unfold panMemLoadByteWord8HOL at h ⊢
  dsimp only at h ⊢
  cases hm : sourceMemory (panByteAlignHOL address) with
  | word value =>
      by_cases hd : sourceDomain (panByteAlignHOL address)
      · rw [← hmem _ hd, hm]
        simpa [hm, hd, hsub _ hd] using h
      · simp [hd] at h

/-- Flapjack-only successful-array-read monotonicity infrastructure. The
premise is pointwise successful-byte preservation, independent of the array
conclusion. The original HOL theorem below derives it from state_rel. -/
private theorem readArray_mono {width : Nat} [NeZero width]
    (source target : BitVec width → Option (BitVec 8))
    (hbyte : ∀ address byte, source address = some byte → target address = some byte)
    (length : Nat) (address : BitVec width) (bytes : List (BitVec 8))
    (h : readBytearrayWordHOL address length source = some bytes) :
    readBytearrayWordHOL address length target = some bytes := by
  induction length generalizing address bytes with
  | zero => simpa [readBytearrayWordHOL] using h
  | succ length ih =>
      change (source address).bind (fun byte =>
        (readBytearrayWordHOL (address + 1) length source).bind
          (fun rest => some (byte :: rest))) = some bytes at h
      change (target address).bind (fun byte =>
        (readBytearrayWordHOL (address + 1) length target).bind
          (fun rest => some (byte :: rest))) = some bytes
      cases hb : source address with
      | none => simp only [hb, Option.bind_none, reduceCtorEq] at h
      | some byte =>
          rw [hbyte address byte hb]
          cases hr : readBytearrayWordHOL (address + 1) length source with
          | none => simp only [hb, hr, Option.bind_some, Option.bind_none, reduceCtorEq] at h
          | some rest =>
              rw [ih (address + 1) rest hr]
              simpa only [hb, hr, Option.bind_some] using h

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

/-- Source1534-1546: the original state relation and a successful source
byte-array read imply the same target bytes. Endianness, domain inclusion and
aligned memory agreement come from the relation, without extra premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_read_bytearray"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelReadBytearray {width : Nat} {σ : Type} [NeZero width]
    (flag : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (bytes : List (BitVec 8)) (address : BitVec width) (length : Nat) :
    panGlobalsStateRelHOLExact flag context source target ∧
      readBytearrayWordHOL address length
        (@panMemLoadByteWord8HOL width _ source.memory source.memaddrs
          (fun a => Classical.propDecidable (source.memaddrs a)) source.be) = some bytes →
    readBytearrayWordHOL address length
        (@panMemLoadByteWord8HOL width _ target.memory target.memaddrs
          (fun a => Classical.propDecidable (target.memaddrs a)) target.be) = some bytes := by
  intro ⟨hrel, hread⟩
  have hbe := hrel.2.2.2.1
  have hsub := hrel.2.2.2.2.2.2.2.2.2.2.1
  have hmem := hrel.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply readArray_mono _ _ ?_ length address bytes hread
  intro a byte hload
  rw [← hbe]
  exact @byteLoad_mono width _ source.memory target.memory source.memaddrs target.memaddrs
    (fun a => Classical.propDecidable (source.memaddrs a))
    (fun a => Classical.propDecidable (target.memaddrs a)) source.be a byte hsub hmem hload

end Flapjack.PanGlobalsReadBytearray
