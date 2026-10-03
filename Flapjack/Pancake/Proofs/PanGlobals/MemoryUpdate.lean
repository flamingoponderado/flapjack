import Flapjack.Pancake.Proofs.PanGlobals.MemStores

/-!
# pan_globals single-address memory updates

Counterpart of `cakeml/pancake/proofs/pan_globalsProofScript.sml:636-690`
(bead `flapjack-pxn.18.5.2.29.1`), the `Store`/`Store32` prerequisites of
`compile_correct`: a load of a nil-well-formed value survives a memory update
outside its address block (`mem_load_disjoint`), and the pan_globals state
relation survives the same update of both memories at a source-domain address
(`state_rel_memory_update`).  HOL's `m⦇a ↦ v⦈` is the pointwise update
`fun x => if x = a then v else m x`, as in the tagged `panMemStoreHOL`.
-/

namespace Flapjack.PanGlobalsMemoryUpdate

open Flapjack
open Flapjack.Compiler.Backend.StackRemove (addresses)
open Flapjack.Pancake.PanLang

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

section Disjoint

variable {width : Nat} [NeZero width] (addrs : BitVec width → Prop) [DecidablePred addrs]

mutual
  /-- Local support: first conjunct of `mem_load_disjoint` for any domain
      decision procedure. -/
  private theorem loadDisjoint_val :
      ∀ (val : ValueHOL width) (addr'' : BitVec width) (memory : BitVec width → HolWordLab width)
        (stcs : StructContextExact) (v : HolWordLab width) (addr' : BitVec width),
        memLoadHOLExact (shapeOfHOLExact val) addr' addrs memory stcs = some val →
        ¬ addresses addr' (sizeOfShapeHOL (shapeOfHOLExact val)) addr'' →
        isWfShapeNilHOL (shapeOfHOLExact val) = true →
        memLoadHOLExact (shapeOfHOLExact val) addr' addrs
          (fun x => if x = addr'' then v else memory x) stcs = some val
    | .val w, addr'', memory, stcs, v, addr', h, hout, _ => by
        simp only [shapeOfHOLExact] at h hout ⊢
        rw [memLoadHOLExact] at h ⊢
        have hne : addr' ≠ addr'' := fun heq => hout (Or.inl heq.symm)
        simp only [if_neg hne]
        exact h
    | .rStruct fields, addr'', memory, stcs, v, addr', h, hout, hwf => by
        simp only [shapeOfHOLExact, sizeOfShapeHOL_comb] at h hout hwf ⊢
        unfold isWfShapeNilHOL at hwf
        rw [isWfShapeExactHOL_comb] at hwf
        rw [memLoadHOLExact] at h ⊢
        cases hs : memLoadsHOLExact (fields.map shapeOfHOLExact) addr' addrs memory stcs with
        | none => rw [hs] at h; cases h
        | some vs =>
            rw [hs] at h
            simp only [Option.some.injEq, ValueHOL.rStruct.injEq] at h
            rw [h] at hs
            rw [loadDisjoint_vals fields addr'' memory stcs v addr' hs hout hwf]
    | .nStruct name fields, _, _, _, _, _, _, _, hwf => by
        simp [shapeOfHOLExact, isWfShapeNilHOL, isWfShapeExactHOL_named,
          structContextLookupHOL_nil] at hwf

  /-- Local support: second conjunct of `mem_load_disjoint`, stated over
      `sizeOfShapesHOL` and the list well-formedness helper. -/
  private theorem loadDisjoint_vals :
      ∀ (vals : List (ValueHOL width)) (addr'' : BitVec width)
        (memory : BitVec width → HolWordLab width)
        (stcs : StructContextExact) (v : HolWordLab width) (addr' : BitVec width),
        memLoadsHOLExact (vals.map shapeOfHOLExact) addr' addrs memory stcs = some vals →
        ¬ addresses addr' (sizeOfShapesHOL (vals.map shapeOfHOLExact)) addr'' →
        isWfShapesExactHOL ([] : Flapjack.Pancake.PanLang.StructContextExact) (vals.map shapeOfHOLExact) = true →
        memLoadsHOLExact (vals.map shapeOfHOLExact) addr' addrs
          (fun x => if x = addr'' then v else memory x) stcs = some vals
    | [], _, _, _, _, _, _, _, _ => by
        simp only [List.map_nil]
        rw [memLoadsHOLExact]
    | val :: vals, addr'', memory, stcs, v, addr', h, hout, hwf => by
        simp only [List.map_cons, sizeOfShapesHOL_cons] at h hout hwf ⊢
        simp only [isWfShapesExactHOL_cons, Bool.and_eq_true] at hwf
        rw [memLoadsHOLExact, sizeOfShapeWithContextHOL_eq_nil _ hwf.1 stcs] at h ⊢
        cases h1 : memLoadHOLExact (shapeOfHOLExact val) addr' addrs memory stcs with
        | none => rw [h1] at h; cases h
        | some val' =>
            cases h2 : memLoadsHOLExact (vals.map shapeOfHOLExact)
                (addr' + bytesInWordHOL width *
                  BitVec.ofNat width (sizeOfShapeHOL (shapeOfHOLExact val)))
                addrs memory stcs with
            | none => rw [h1, h2] at h; cases h
            | some vals' =>
                rw [h1, h2] at h
                simp only [Option.some.injEq, List.cons.injEq] at h
                obtain ⟨hv, hvs⟩ := h
                rw [hv] at h1
                rw [hvs] at h2
                have hout1 : ¬ addresses addr' (sizeOfShapeHOL (shapeOfHOLExact val)) addr'' :=
                  fun hin => hout ((PanGlobalsMemStores.addresses_add _ _ addr' addr'').2
                    (Or.inl hin))
                have hout2 : ¬ addresses
                    (addr' + bytesInWordHOL width *
                      BitVec.ofNat width (sizeOfShapeHOL (shapeOfHOLExact val)))
                    (sizeOfShapesHOL (vals.map shapeOfHOLExact)) addr'' :=
                  fun hin => hout ((PanGlobalsMemStores.addresses_add _ _ addr' addr'').2
                    (Or.inr hin))
                rw [loadDisjoint_val val addr'' memory stcs v addr' h1 hout1 hwf.1,
                  loadDisjoint_vals vals addr'' memory stcs v _ h2 hout2 hwf.2]
end

end Disjoint

/-- Local support: `SUM (MAP (size_of_shape o shape_of))` is `sizeOfShapesHOL`. -/
private theorem sum_map_size {width : Nat} [NeZero width] (vals : List (ValueHOL width)) :
    (vals.map (fun v => sizeOfShapeHOL (shapeOfHOLExact v))).sum =
      sizeOfShapesHOL (vals.map shapeOfHOLExact) := by
  induction vals with
  | nil => simp
  | cons v vs ih => simp only [List.map_cons, List.sum_cons, sizeOfShapesHOL_cons, ih]

/-- Local support: `EVERY is_wf_shape_nil` as the list helper. -/
private theorem every_wf_iff : ∀ shapes : List ShapeHOL,
    (∀ s ∈ shapes, isWfShapeNilHOL s = true) ↔ isWfShapesExactHOL ([] : Flapjack.Pancake.PanLang.StructContextExact) shapes = true
  | [] => by simp
  | shape :: rest => by
      rw [isWfShapesExactHOL_cons, Bool.and_eq_true, ← every_wf_iff rest]
      simp only [List.forall_mem_cons, isWfShapeNilHOL]

/-- Exact HOL `mem_load_disjoint` (`pan_globalsProofScript.sml:636-674`), both
    conjuncts.  `addr'' ∉ addresses ...` is the negated predicate; `EVERY` is
    list membership; `size_of_shape o shape_of` is the composed function. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_load_disjoint"
  (words_as_type_indexed_bitvec)]
theorem memLoadDisjointHOL {width : Nat} [NeZero width] :
    (∀ (val : ValueHOL width) (addr'' : BitVec width) (memory : BitVec width → HolWordLab width)
      (stcs : StructContextExact) (v : HolWordLab width) (addr' : BitVec width)
      (addrs : BitVec width → Prop),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      memLoadHOLExact (shapeOfHOLExact val) addr' addrs memory stcs = some val ∧
        ¬ addresses addr' (sizeOfShapeHOL (shapeOfHOLExact val)) addr'' ∧
        isWfShapeNilHOL (shapeOfHOLExact val) = true →
        memLoadHOLExact (shapeOfHOLExact val) addr' addrs
          (fun x => if x = addr'' then v else memory x) stcs = some val) ∧
    (∀ (vals : List (ValueHOL width)) (addr'' : BitVec width)
      (memory : BitVec width → HolWordLab width)
      (stcs : StructContextExact) (v : HolWordLab width) (addr' : BitVec width)
      (addrs : BitVec width → Prop),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      memLoadsHOLExact (vals.map shapeOfHOLExact) addr' addrs memory stcs = some vals ∧
        ¬ addresses addr' (vals.map (fun v => sizeOfShapeHOL (shapeOfHOLExact v))).sum addr'' ∧
        (∀ s ∈ vals.map shapeOfHOLExact, isWfShapeNilHOL s = true) →
        memLoadsHOLExact (vals.map shapeOfHOLExact) addr' addrs
          (fun x => if x = addr'' then v else memory x) stcs = some vals) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro val addr'' memory stcs v addr' addrs ⟨h, hout, hwf⟩
    exact loadDisjoint_val addrs val addr'' memory stcs v addr' h hout hwf
  · rintro vals addr'' memory stcs v addr' addrs ⟨h, hout, hwf⟩
    rw [sum_map_size] at hout
    exact loadDisjoint_vals addrs vals addr'' memory stcs v addr' h hout
      ((every_wf_iff _).1 hwf)

/-- Exact HOL `state_rel_memory_update` (`pan_globalsProofScript.sml:676-690`):
    updating both memories at the same source-domain address with the same
    word preserves `state_rel T`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_memory_update"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelMemoryUpdateHOL {width : Nat} {σ : Type} [NeZero width]
    (ctxt : PanGlobalsContextExact width) (s t : PanSemStateFiniteExact width σ)
    (addr' : BitVec width) (h : HolWordLab width) :
    panGlobalsStateRelHOLExact true ctxt s t ∧ s.memaddrs addr' →
      panGlobalsStateRelHOLExact true ctxt
        { s with memory := fun x => if x = addr' then h else s.memory x }
        { t with memory := fun x => if x = addr' then h else t.memory x } := by
  classical
  rintro ⟨hrel, hin⟩
  rcases hrel with ⟨ht, hl, hb, hbe, he, hc, hs, hts, hg, hgw, hm, hsh, hmem, hffi, hcode, hd⟩
  refine ⟨ht, hl, hb, hbe, he, hc, hs, hts, ?_, hgw, hm, hsh, ?_, hffi, hcode, hd⟩
  · intro name value hlookup
    obtain ⟨address, hctx, hwf, hload, hdis, halign⟩ := hg name value hlookup
    refine ⟨address, hctx, hwf, ?_, hdis, halign⟩
    exact memLoadDisjointHOL.1 value addr' t.memory [] h (t.topAddr - address) t.memaddrs
      ⟨hload, hdis addr' hin, hwf⟩
  · intro a ha
    show (if a = addr' then h else s.memory a) = (if a = addr' then h else t.memory a)
    rw [hmem a ha]

end Flapjack.PanGlobalsMemoryUpdate
