import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

/-!
# pan_globals `ShMemLoad` prerequisites

Counterpart of `cakeml/pancake/proofs/pan_globalsProofScript.sml:737-755`
(bead `flapjack-pxn.18.5.2.30.1`): the fresh-name inequality `v_neq_v'` and
the projection `FLOOKUP_globals_val_state_rel` of the global-variable conjunct
of `state_rel`, both used by `Resume compile_correct[ShMemLoad]`.
-/

namespace Flapjack.PanGlobalsShMemLoadLemmas

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Canonical state roundtrips, re-exported for the relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for the relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Exact HOL `v_neq_v'` (`pan_globalsProofScript.sml:737-742`, local):
    `v ≠ v ^ «'»`, with `^` the untagged `mlstrAppend` and `«'»` the
    one-character `mlstring`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "v_neq_v'"]
theorem vNeqV' (v : MlS) : v ≠ mlstrAppend v (Flapjack.Basis.Pure.MlString.ofString "'") := by
  intro h
  have := congrArg (fun m => (Flapjack.Basis.Pure.MlString.MlString.explode m).length) h
  simp [mlstrAppend, Flapjack.Basis.Pure.MlString.ofString,
    Flapjack.Basis.Pure.MlString.MlString.explode_implode] at this

/-- Exact HOL `FLOOKUP_globals_val_state_rel` (`pan_globalsProofScript.sml:744-755`).
    `DISJOINT s.memaddrs A` over predicate sets is `∀ x, s.memaddrs x → ¬ A x`,
    the rendering used by `state_rel`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FLOOKUP_globals_val_state_rel"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem flookupGlobalsValStateRelHOL {width : Nat} {σ : Type} [NeZero width]
    (s t : PanSemStateFiniteExact width σ) (nm : MlS) (v : HolWordLab width) (b : Bool)
    (ctxt : PanGlobalsContextExact width) :
    letI : DecidablePred t.memaddrs := fun a => Classical.propDecidable (t.memaddrs a)
    s.globals.lookup nm = some (.val v) ∧ panGlobalsStateRelHOLExact b ctxt s t →
      ∃ addr_diff, ctxt.globals.lookup nm = some (shapeOfHOLExact (.val v), addr_diff) ∧
        memLoadHOLExact (shapeOfHOLExact (.val v)) (t.topAddr - addr_diff) t.memaddrs t.memory
          ([] : StructContextExact) = some (.val v) ∧
        (∀ x, s.memaddrs x →
          ¬ addresses (t.topAddr - addr_diff) (sizeOfShapeHOL (shapeOfHOLExact (.val v))) x) ∧
        panGlobalsByteAlignedHOL addr_diff := by
  rintro ⟨hlookup, hrel⟩
  obtain ⟨addr_diff, hctx, _, hload, hdis, halign⟩ :=
    hrel.2.2.2.2.2.2.2.2.1 nm (.val v) hlookup
  exact ⟨addr_diff, hctx, hload, hdis, halign⟩

end Flapjack.PanGlobalsShMemLoadLemmas
