import Flapjack.Pancake.Proofs.PanGlobals.ByteStore

/-!
# pan_globals `state_rel_write_bytearray`

Counterpart of `cakeml/pancake/proofs/pan_globalsProofScript.sml:1571-1593`
(bead `flapjack-pxn.18.5.2.35.3`), the byte-array write prerequisite of
`Resume compile_correct[ExtCall]`.
-/

namespace Flapjack.PanGlobalsWriteBytearray

open Flapjack
open Flapjack.Pancake.PanLang

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

/-- Exact HOL `state_rel_write_bytearray` (`pan_globalsProofScript.sml:1571-1593`).
    HOL's leading `∀a` binds a variable that does not occur in the statement
    (of an arbitrary, hence inhabited, HOL type), so it is omitted; the other
    binders `ls ctxt s t sz nbw bs` are kept in order.  Memory-domain membership
    is decided classically inside the statement, with no added premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_write_bytearray"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelWriteBytearrayHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (ls : Bool) (ctxt : PanGlobalsContextExact width) (s t : PanSemStateFiniteExact width σ)
      (sz : BitVec width) (nbw bs : List (BitVec 8)),
      panGlobalsStateRelHOLExact ls ctxt s t ∧
        readBytearrayWordHOL sz nbw.length
          (@panMemLoadByteWord8HOL width _ s.memory s.memaddrs
            (fun a => Classical.propDecidable (s.memaddrs a)) s.be) = some bs →
      panGlobalsStateRelHOLExact ls ctxt
        { s with memory := (@panWriteBytearrayWord8HOL width _ sz nbw s.memory s.memaddrs
            (fun a => Classical.propDecidable (s.memaddrs a)) s.be) }
        { t with memory := (@panWriteBytearrayWord8HOL width _ sz nbw t.memory t.memaddrs
            (fun a => Classical.propDecidable (t.memaddrs a)) t.be) } := by
  intro ls ctxt s t sz nbw
  induction nbw generalizing sz with
  | nil =>
      intro bs ⟨hrel, _⟩
      exact hrel
  | cons b rest ih =>
      intro bs ⟨hrel, hread⟩
      simp only [List.length_cons, readBytearrayWordHOL] at hread
      cases hbyte : @panMemLoadByteWord8HOL width _ s.memory s.memaddrs
          (fun a => Classical.propDecidable (s.memaddrs a)) s.be sz with
      | none => rw [hbyte] at hread; cases hread
      | some byte0 =>
          rw [hbyte] at hread
          cases htail : readBytearrayWordHOL (sz + 1) rest.length
              (@panMemLoadByteWord8HOL width _ s.memory s.memaddrs
                (fun a => Classical.propDecidable (s.memaddrs a)) s.be) with
          | none => rw [htail] at hread; cases hread
          | some bs' =>
              have hrel1 := ih (sz + 1) bs' ⟨hrel, htail⟩
              have hdom : s.memaddrs (panByteAlignHOL (width := width) sz) := by
                unfold panMemLoadByteWord8HOL at hbyte
                cases hcell : s.memory (panByteAlignHOL (width := width) sz) with
                | word cell =>
                    simp only [hcell] at hbyte
                    by_cases hd : s.memaddrs (panByteAlignHOL (width := width) sz)
                    · exact hd
                    · simp [hd] at hbyte
              obtain ⟨m', hstore⟩ : ∃ m', @panMemStoreByteWord8HOL width _
                  (@panWriteBytearrayWord8HOL width _ (sz + 1) rest s.memory s.memaddrs
                    (fun a => Classical.propDecidable (s.memaddrs a)) s.be)
                  s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be sz b =
                    some m' := by
                unfold panMemStoreByteWord8HOL
                simp only [if_pos hdom]
                exact ⟨_, rfl⟩
              obtain ⟨m'', htstore, hrel2⟩ :=
                PanGlobalsByteStore.stateRelMemStoreByte ls ctxt _ _ sz b m' ⟨hrel1, hstore⟩
              have hs : @panWriteBytearrayWord8HOL width _ sz (b :: rest) s.memory s.memaddrs
                  (fun a => Classical.propDecidable (s.memaddrs a)) s.be = m' := by
                rw [panWriteBytearrayWord8HOL]
                exact (congrArg (fun o => match o with | some u => u | none => s.memory)
                  hstore).trans rfl
              have ht : @panWriteBytearrayWord8HOL width _ sz (b :: rest) t.memory t.memaddrs
                  (fun a => Classical.propDecidable (t.memaddrs a)) t.be = m'' := by
                rw [panWriteBytearrayWord8HOL]
                exact (congrArg (fun o => match o with | some u => u | none => t.memory)
                  htstore).trans rfl
              rw [hs, ht]
              exact hrel2

end Flapjack.PanGlobalsWriteBytearray
