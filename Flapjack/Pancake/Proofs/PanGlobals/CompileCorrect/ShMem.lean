import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.ShMemLoadLemmas
import Flapjack.Pancake.Proofs.PanGlobals.MemoryUpdate
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Semantics.PanSem.FiniteSupportStep

/-!
# pan_globals `compile_correct`: the `ShMemLoad` and `ShMemStore` cases

`Resume compile_correct[ShMemLoad]` and `[ShMemStore]`
(`cakeml/pancake/proofs/pan_globalsProofScript.sml:757-858`, bead
`flapjack-pxn.18.5.2.30`).  Both constructors have no recursive sub-program, so
the `evaluate_ind` conjuncts carry no induction hypothesis; each theorem states
HOL's goal for its constructor, unfolded exactly as in the leaf cases of
`Base.lean`.

Every `ShMemStore` compiles to the same constructor with compiled expressions.
HOL resumes `ShMemLoad` with a `Cases` on the `varkind` constructor: the
`Local` sub-case keeps the constructor and only compiles the address; the
`Global` sub-case is lowered to a nested `Dec` that loads the address into a
fresh local, reads shared memory into a `name'` temporary, and stores the result
into the global's memory block, restoring both locals afterwards.  The source
address/value evaluations are lifted by the tagged `compileExpCorrectHOL`
(`compile_exp_correct`).

This module ports `ShMemStore` and the `ShMemLoad` `Local` sub-case.  The
`ShMemLoad` `Global` sub-case and the complete Local/Global case assembly live
in the sibling `ShMemGlobal` module.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace PanGlobalsCompileCorrectShMemWitnesses

/-- Canonical state roundtrip, re-exported for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context


end PanGlobalsCompileCorrectShMemWitnesses

namespace PanGlobalsCompileCorrect

/-- Flapjack-only support: `ofExact` is proof-irrelevant in its finite-support
    argument, so on `state.toExact` it recovers `state`.  HOL has no separate
    declaration for this carrier repacking. -/
@[simp] theorem ofExact_toExact_any {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (h : state.toExact.FiniteSupport) :
    ofExact state.toExact h = state := by
  rw [show h = state.toExact_finiteSupport from Subsingleton.elim _ _]
  exact PanSemStateFiniteExact.ofExact_toExact state

/-- Flapjack-only support: repacking a `toExact` state whose `ffi` was updated
    recovers the finite carrier with the same `ffi` update. -/
@[simp] theorem ofExact_ffiUpdate {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (f : HolFfiState σ)
    (h : ({state.toExact with ffi := f}).FiniteSupport) :
    ofExact {state.toExact with ffi := f} h = {state with ffi := f} := by
  cases state
  rfl

/-- Flapjack-only support: replacing the `ffi` field of both related states
    with the same value preserves the relation.  HOL's relation only mentions
    `ffi` in the equality conjunct, so no HOL declaration is needed. -/
theorem stateRelFfiUpdateHOL {width : Nat} {σ : Type} [NeZero width]
    (flag : Bool) (ctxt : PanGlobalsContextExact width)
    (s t : PanSemStateFiniteExact width σ) (f : HolFfiState σ) :
    panGlobalsStateRelHOLExact flag ctxt s t →
    panGlobalsStateRelHOLExact flag ctxt {s with ffi := f} {t with ffi := f} := by
  intro hrel
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, _, h15, h16, h17, h18,
    h19⟩ := hrel
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, rfl, h15, h16, h17, h18,
    h19⟩

/-- Flapjack-only support: the relation at flag `false` makes the locals
    equality conjunct vacuous, so the true-flag relation implies it. -/
theorem stateRelFlagFalseHOL {width : Nat} {σ : Type} [NeZero width]
    (ctxt : PanGlobalsContextExact width)
    (s t : PanSemStateFiniteExact width σ) :
    panGlobalsStateRelHOLExact true ctxt s t →
    panGlobalsStateRelHOLExact false ctxt s t := by
  intro hrel
  obtain ⟨h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := hrel
  exact ⟨h1, (fun h => absurd h (by simp)), h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19⟩

/-- Flapjack-only support: `ofExact` ignores its finite-support proof. -/
@[simp] theorem ofExact_proof_irrel {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h1 h2 : state.FiniteSupport) :
    ofExact state h1 = ofExact state h2 := by
  rw [Subsingleton.elim h1 h2]

/-- Flapjack-only wrapper: `shMemStoreHOLExact` on a finite carrier's
    forgetful projection with the classical shared-memory decision. -/
noncomputable abbrev shMemStoreFin {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (word address : RiscV.Word width)
    (nb : Nat) : Option (PanSemResultExact width) × PanSemStateExact width σ :=
  @shMemStoreHOLExact width σ _ state.toExact
    (fun a => Classical.propDecidable (state.shMemaddrs a)) word address nb

/-- Flapjack-only wrapper: `shMemLoadHOLFiniteExact` with the classical
    shared-memory decision, exposing the same form used by the tagged
    `evaluateHOLFiniteState_shMemLoad_source` equation. -/
noncomputable abbrev shMemLoadFin {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (kind : VarKind) (name : MlS)
    (addr : RiscV.Word width) (nb : Nat) :
    Option (PanSemResultExact width) × PanSemStateFiniteExact width σ :=
  @shMemLoadHOLFiniteExact width σ _ state
    (fun a => Classical.propDecidable (state.shMemaddrs a)) kind name addr nb

/-- Flapjack-only support: a successful `ShMemStore` step preserves the
    pan_globals relation between the two memories.  The store only reads
    `shMemaddrs` and `ffi`, both equal under the relation; a final event leaves
    the states untouched (relation at flag `false`), an FFI return updates both
    `ffi` fields to the same value.  HOL has no separate declaration for this
    composed support. -/
theorem shMemStoreRelationHOL {width : Nat} {σ : Type} [NeZero width]
    (ctxt : PanGlobalsContextExact width)
    (s t : PanSemStateFiniteExact width σ)
    (hrel : panGlobalsStateRelHOLExact true ctxt s t)
    (bytes addr : RiscV.Word width) (nb : Nat) :
    (shMemStoreFin t bytes addr nb).1 =
        (shMemStoreFin s bytes addr nb).1 ∧
      panGlobalsStateRelHOLExact
        (goodResHOL (shMemStoreFin s bytes addr nb).1) ctxt
        (ofExact (shMemStoreFin s bytes addr nb).2
          (@shMemStoreHOLExact_finiteSupport width σ _ s.toExact
            (fun a => Classical.propDecidable (s.shMemaddrs a)) bytes addr nb
            s.toExact_finiteSupport))
        (ofExact (shMemStoreFin t bytes addr nb).2
          (@shMemStoreHOLExact_finiteSupport width σ _ t.toExact
            (fun a => Classical.propDecidable (t.shMemaddrs a)) bytes addr nb
            t.toExact_finiteSupport)) := by
  classical
  have hffi : s.ffi = t.ffi := hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hshmem : s.shMemaddrs = t.shMemaddrs := hrel.2.2.2.2.2.2.2.2.2.2.2.1
  have hffi' : t.toExact.ffi = s.toExact.ffi := hffi.symm
  constructor
  · by_cases hnb : nb = 0
    · by_cases hmem : s.shMemaddrs addr
      · have hmemT : t.shMemaddrs addr := by rw [← hshmem]; exact hmem
        cases hcall : callFFIHOL s.toExact.ffi (.sharedMem .mappedWrite)
            [BitVec.ofNat 8 nb]
            (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) with
        | final event =>
          have hcallT : callFFIHOL t.toExact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) =
              HolFfiResult.final event := by rw [hffi']; exact hcall
          simp only [shMemStoreFin, shMemStoreHOLExact, if_pos hnb,
            if_pos (show s.toExact.shMemaddrs addr from hmem),
            if_pos (show t.toExact.shMemaddrs addr from hmemT), hcall, hcallT]
        | ret newFfi newBytes =>
          have hcallT : callFFIHOL t.toExact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) =
              HolFfiResult.ret newFfi newBytes := by rw [hffi']; exact hcall
          simp only [shMemStoreFin, shMemStoreHOLExact, if_pos hnb,
            if_pos (show s.toExact.shMemaddrs addr from hmem),
            if_pos (show t.toExact.shMemaddrs addr from hmemT), hcall, hcallT]
      · have hmemT : ¬ t.shMemaddrs addr := by rw [← hshmem]; exact hmem
        simp only [shMemStoreFin, shMemStoreHOLExact, if_pos hnb,
          if_neg (show ¬ s.toExact.shMemaddrs addr from hmem),
          if_neg (show ¬ t.toExact.shMemaddrs addr from hmemT)]
    · by_cases hmem : s.shMemaddrs (panByteAlignHOL addr)
      · have hmemT : t.shMemaddrs (panByteAlignHOL addr) := by rw [← hshmem]; exact hmem
        cases hcall : callFFIHOL s.toExact.ffi (.sharedMem .mappedWrite)
            [BitVec.ofNat 8 nb]
            ((panWordToBytesHOL bytes false).take nb ++ panWordToBytesHOL addr false) with
        | final event =>
          have hcallT : callFFIHOL t.toExact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              ((panWordToBytesHOL bytes false).take nb ++ panWordToBytesHOL addr false) =
              HolFfiResult.final event := by rw [hffi']; exact hcall
          simp only [shMemStoreFin, shMemStoreHOLExact, if_neg hnb,
            if_pos (show s.toExact.shMemaddrs (panByteAlignHOL addr) from hmem),
            if_pos (show t.toExact.shMemaddrs (panByteAlignHOL addr) from hmemT),
            hcall, hcallT]
        | ret newFfi newBytes =>
          have hcallT : callFFIHOL t.toExact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              ((panWordToBytesHOL bytes false).take nb ++ panWordToBytesHOL addr false) =
              HolFfiResult.ret newFfi newBytes := by rw [hffi']; exact hcall
          simp only [shMemStoreFin, shMemStoreHOLExact, if_neg hnb,
            if_pos (show s.toExact.shMemaddrs (panByteAlignHOL addr) from hmem),
            if_pos (show t.toExact.shMemaddrs (panByteAlignHOL addr) from hmemT),
            hcall, hcallT]
      · have hmemT : ¬ t.shMemaddrs (panByteAlignHOL addr) := by rw [← hshmem]; exact hmem
        simp only [shMemStoreFin, shMemStoreHOLExact, if_neg hnb,
          if_neg (show ¬ s.toExact.shMemaddrs (panByteAlignHOL addr) from hmem),
          if_neg (show ¬ t.toExact.shMemaddrs (panByteAlignHOL addr) from hmemT)]
  · by_cases hnb : nb = 0
    · by_cases hmem : s.shMemaddrs addr
      · have hmemT : t.shMemaddrs addr := by rw [← hshmem]; exact hmem
        cases hcall : callFFIHOL s.toExact.ffi (.sharedMem .mappedWrite)
            [BitVec.ofNat 8 nb]
            (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) with
        | final event =>
          have hcallT : callFFIHOL t.toExact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) =
              HolFfiResult.final event := by rw [hffi']; exact hcall
          simp only [shMemStoreFin, shMemStoreHOLExact, if_pos hnb,
            if_pos (show s.toExact.shMemaddrs addr from hmem),
            if_pos (show t.toExact.shMemaddrs addr from hmemT),
            hcall, hcallT, goodResHOL]
          change panGlobalsStateRelHOLExact false ctxt s t
          exact stateRelFlagFalseHOL ctxt s t hrel
        | ret newFfi' newBytes =>
          have hcallT : callFFIHOL t.toExact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) =
              HolFfiResult.ret newFfi' newBytes := by rw [hffi']; exact hcall
          simp only [shMemStoreFin, shMemStoreHOLExact, if_pos hnb,
            if_pos (show s.toExact.shMemaddrs addr from hmem),
            if_pos (show t.toExact.shMemaddrs addr from hmemT),
            hcall, hcallT, goodResHOL]
          exact stateRelFfiUpdateHOL true ctxt s t newFfi' hrel
      · have hmemT : ¬ t.shMemaddrs addr := by rw [← hshmem]; exact hmem
        simp only [shMemStoreFin, shMemStoreHOLExact, if_pos hnb,
          if_neg (show ¬ s.toExact.shMemaddrs addr from hmem),
          if_neg (show ¬ t.toExact.shMemaddrs addr from hmemT),
          ofExact_toExact_any, goodResHOL]
        change panGlobalsStateRelHOLExact true ctxt s t
        exact hrel
    · by_cases hmem : s.shMemaddrs (panByteAlignHOL addr)
      · have hmemT : t.shMemaddrs (panByteAlignHOL addr) := by rw [← hshmem]; exact hmem
        cases hcall : callFFIHOL s.toExact.ffi (.sharedMem .mappedWrite)
            [BitVec.ofNat 8 nb]
            ((panWordToBytesHOL bytes false).take nb ++ panWordToBytesHOL addr false) with
        | final event =>
          have hcallT : callFFIHOL t.toExact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              ((panWordToBytesHOL bytes false).take nb ++ panWordToBytesHOL addr false) =
              HolFfiResult.final event := by rw [hffi']; exact hcall
          simp only [shMemStoreFin, shMemStoreHOLExact, if_neg hnb,
            if_pos (show s.toExact.shMemaddrs (panByteAlignHOL addr) from hmem),
            if_pos (show t.toExact.shMemaddrs (panByteAlignHOL addr) from hmemT),
            hcall, hcallT, goodResHOL]
          change panGlobalsStateRelHOLExact false ctxt s t
          exact stateRelFlagFalseHOL ctxt s t hrel
        | ret newFfi' newBytes =>
          have hcallT : callFFIHOL t.toExact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              ((panWordToBytesHOL bytes false).take nb ++ panWordToBytesHOL addr false) =
              HolFfiResult.ret newFfi' newBytes := by rw [hffi']; exact hcall
          simp only [shMemStoreFin, shMemStoreHOLExact, if_neg hnb,
            if_pos (show s.toExact.shMemaddrs (panByteAlignHOL addr) from hmem),
            if_pos (show t.toExact.shMemaddrs (panByteAlignHOL addr) from hmemT),
            hcall, hcallT, goodResHOL]
          exact stateRelFfiUpdateHOL true ctxt s t newFfi' hrel
      · have hmemT : ¬ t.shMemaddrs (panByteAlignHOL addr) := by rw [← hshmem]; exact hmem
        simp only [shMemStoreFin, shMemStoreHOLExact, if_neg hnb,
          if_neg (show ¬ s.toExact.shMemaddrs (panByteAlignHOL addr) from hmem),
          if_neg (show ¬ t.toExact.shMemaddrs (panByteAlignHOL addr) from hmemT),
          ofExact_toExact_any, goodResHOL]
        change panGlobalsStateRelHOLExact true ctxt s t
        exact hrel

/-- Flapjack-only support: a successful local `ShMemLoad` step preserves the
    pan_globals relation.  The load reads `shMemaddrs`/`ffi` and writes `locals`
    through `set_kvar Local`, all equal under the relation; a final event clears
    both local maps (relation at flag `false`), an FFI return installs the same
    word into both (relation at flag `true`), and a failed domain test leaves
    both states untouched.  HOL has no separate declaration for this support. -/
theorem shMemLoadLocalRelationHOL {width : Nat} {σ : Type} [NeZero width]
    (ctxt : PanGlobalsContextExact width)
    (s t : PanSemStateFiniteExact width σ)
    (hrel : panGlobalsStateRelHOLExact true ctxt s t)
    (name : MlS) (addr : RiscV.Word width) (nb : Nat) :
    (shMemLoadFin t .local name addr nb).1 =
        (shMemLoadFin s .local name addr nb).1 ∧
      panGlobalsStateRelHOLExact
        (goodResHOL (shMemLoadFin s .local name addr nb).1) ctxt
        (shMemLoadFin s .local name addr nb).2
        (shMemLoadFin t .local name addr nb).2 := by
  classical
  have hshmem : s.shMemaddrs = t.shMemaddrs := hrel.2.2.2.2.2.2.2.2.2.2.2.1
  have hffi : s.ffi = t.ffi := hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc : s.locals = t.locals := hrel.2.1 rfl
  constructor
  · by_cases hnb : nb = 0
    · by_cases hmem : s.shMemaddrs addr
      · have hmemT : t.shMemaddrs addr := by rw [← hshmem]; exact hmem
        cases hcall : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
            (panWordToBytesHOL addr false) with
        | final event =>
          have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL addr false) = HolFfiResult.final event := by
            rw [← hffi]; exact hcall
          simp only [shMemLoadHOLFiniteExact, if_pos hnb, if_pos hmem, if_pos hmemT,
            hcall, hcallT]
        | ret newFfi newBytes =>
          have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL addr false) = HolFfiResult.ret newFfi newBytes := by
            rw [← hffi]; exact hcall
          simp only [shMemLoadHOLFiniteExact, if_pos hnb, if_pos hmem, if_pos hmemT,
            hcall, hcallT]
      · have hmemT : ¬ t.shMemaddrs addr := by rw [← hshmem]; exact hmem
        simp only [shMemLoadHOLFiniteExact, if_pos hnb, if_neg hmem, if_neg hmemT]
    · by_cases hmem : s.shMemaddrs (panByteAlignHOL addr)
      · have hmemT : t.shMemaddrs (panByteAlignHOL addr) := by rw [← hshmem]; exact hmem
        cases hcall : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
            (panWordToBytesHOL addr false) with
        | final event =>
          have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL addr false) = HolFfiResult.final event := by
            rw [← hffi]; exact hcall
          simp only [shMemLoadHOLFiniteExact, if_neg hnb, if_pos hmem, if_pos hmemT,
            hcall, hcallT]
        | ret newFfi newBytes =>
          have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL addr false) = HolFfiResult.ret newFfi newBytes := by
            rw [← hffi]; exact hcall
          simp only [shMemLoadHOLFiniteExact, if_neg hnb, if_pos hmem, if_pos hmemT,
            hcall, hcallT]
      · have hmemT : ¬ t.shMemaddrs (panByteAlignHOL addr) := by rw [← hshmem]; exact hmem
        simp only [shMemLoadHOLFiniteExact, if_neg hnb, if_neg hmem, if_neg hmemT]
  · by_cases hnb : nb = 0
    · by_cases hmem : s.shMemaddrs addr
      · have hmemT : t.shMemaddrs addr := by rw [← hshmem]; exact hmem
        cases hcall : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
            (panWordToBytesHOL addr false) with
        | final event =>
          have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL addr false) = HolFfiResult.final event := by
            rw [← hffi]; exact hcall
          simp only [shMemLoadHOLFiniteExact, if_pos hnb, if_pos hmem, if_pos hmemT,
            hcall, hcallT, goodResHOL, emptyLocalsHOLFinite]
          exact (Flapjack.PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL ctxt s t false).1 hrel
        | ret newFfi newBytes =>
          have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL addr false) = HolFfiResult.ret newFfi newBytes := by
            rw [← hffi]; exact hcall
          simp only [shMemLoadHOLFiniteExact, if_pos hnb, if_pos hmem, if_pos hmemT,
            hcall, hcallT, goodResHOL]
          exact stateRelFfiUpdateHOL true ctxt (s.setVarHOLFinite name _)
            (t.setVarHOLFinite name _) newFfi
            (Flapjack.PanGlobalsStateRelationLocals.stateRelSetVarHOL ctxt s t true name _
              hrel)
      · have hmemT : ¬ t.shMemaddrs addr := by rw [← hshmem]; exact hmem
        simp only [shMemLoadHOLFiniteExact, if_pos hnb, if_neg hmem, if_neg hmemT,
          goodResHOL]
        exact hrel
    · by_cases hmem : s.shMemaddrs (panByteAlignHOL addr)
      · have hmemT : t.shMemaddrs (panByteAlignHOL addr) := by rw [← hshmem]; exact hmem
        cases hcall : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
            (panWordToBytesHOL addr false) with
        | final event =>
          have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL addr false) = HolFfiResult.final event := by
            rw [← hffi]; exact hcall
          simp only [shMemLoadHOLFiniteExact, if_neg hnb, if_pos hmem, if_pos hmemT,
            hcall, hcallT, goodResHOL, emptyLocalsHOLFinite]
          exact (Flapjack.PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL ctxt s t false).1 hrel
        | ret newFfi newBytes =>
          have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL addr false) = HolFfiResult.ret newFfi newBytes := by
            rw [← hffi]; exact hcall
          simp only [shMemLoadHOLFiniteExact, if_neg hnb, if_pos hmem, if_pos hmemT,
            hcall, hcallT, goodResHOL]
          exact stateRelFfiUpdateHOL true ctxt (s.setVarHOLFinite name _)
            (t.setVarHOLFinite name _) newFfi
            (Flapjack.PanGlobalsStateRelationLocals.stateRelSetVarHOL ctxt s t true name _
              hrel)
      · have hmemT : ¬ t.shMemaddrs (panByteAlignHOL addr) := by rw [← hshmem]; exact hmem
        simp only [shMemLoadHOLFiniteExact, if_neg hnb, if_neg hmem, if_neg hmemT,
          goodResHOL]
        exact hrel

/-- `ShMemStore` case of HOL `compile_correct`.  HOL's printed `evaluate_ind`
    `ShMemStore` conjunct is `!op ad e s. P (ShMemStore op ad e,s)`; there is no
    sub-program, so the theorem has no induction hypothesis and unfolds
    `P = compileCorrectGoal` for the constructor. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_ShMemStore {width : Nat} {σ : Type} [NeZero width]
    (operator : OpSize) (address value : ExpHOL width)
    (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.shMemStore operator address value) = (res, s') ∧
        res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t
          (compileProgExactHOL ctxt (.shMemStore operator address value)) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  intro res ctxt t s' ⟨hrel, hev, hne⟩
  have hcompile : compileProgExactHOL ctxt (.shMemStore operator address value) =
      .shMemStore operator (compileExpExactHOL ctxt address)
        (compileExpExactHOL ctxt value) := by
    simp [compileProgExactHOL]
  rw [evaluateHOLFiniteState_shMemStore_total] at hev
  rw [hcompile, evaluateHOLFiniteState_shMemStore_total]
  dsimp only at hev ⊢
  cases haddrS : (@evalHOLExact width σ _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a)) address) with
  | none =>
      simp only [haddrS] at hev
      exact absurd (Prod.mk.inj hev).1.symm hne
  | some av =>
      cases av with
      | rStruct fields =>
          simp only [haddrS] at hev
          exact absurd (Prod.mk.inj hev).1.symm hne
      | nStruct name fields =>
          simp only [haddrS] at hev
          exact absurd (Prod.mk.inj hev).1.symm hne
      | val avp =>
          cases avp with
          | word addr =>
              cases hvalS : (@evalHOLExact width σ _ s.toExact
              (fun a => Classical.propDecidable (s.memaddrs a)) value) with
              | none =>
                  simp only [haddrS, hvalS] at hev
                  exact absurd (Prod.mk.inj hev).1.symm hne
              | some vv =>
                  cases vv with
                  | rStruct fields =>
                      simp only [haddrS, hvalS] at hev
                      exact absurd (Prod.mk.inj hev).1.symm hne
                  | nStruct name fields =>
                      simp only [haddrS, hvalS] at hev
                      exact absurd (Prod.mk.inj hev).1.symm hne
                  | val vvp =>
                      cases vvp with
                      | word bytes =>
                          have haddrT : @evalHOLExact width σ _ t.toExact
                              (fun a => Classical.propDecidable (t.memaddrs a))
                              (compileExpExactHOL ctxt address) =
                              some (.val (.word addr)) :=
                            Flapjack.PanGlobalsCompileExpCorrect.compileExpCorrectHOL s address (.val (.word addr)) ctxt t
                              ⟨hrel, haddrS⟩
                          have hvalT : @evalHOLExact width σ _ t.toExact
                              (fun a => Classical.propDecidable (t.memaddrs a))
                              (compileExpExactHOL ctxt value) =
                              some (.val (.word bytes)) :=
                            Flapjack.PanGlobalsCompileExpCorrect.compileExpCorrectHOL s value (.val (.word bytes)) ctxt t
                              ⟨hrel, hvalS⟩
                          simp only [haddrS, hvalS, haddrT, hvalT] at hev ⊢
                          obtain ⟨hresEq, hs'Eq⟩ := Prod.mk.inj hev
                          obtain ⟨houtEq, hrelOut⟩ :=
                            shMemStoreRelationHOL ctxt s t hrel bytes addr (nbOpHOL operator)
                          refine ⟨ofExact (shMemStoreFin t bytes addr
                            (nbOpHOL operator)).2
                            (@shMemStoreHOLExact_finiteSupport width σ _ t.toExact
                              (fun a => Classical.propDecidable (t.shMemaddrs a)) bytes addr
                              (nbOpHOL operator) t.toExact_finiteSupport), ?_, ?_⟩
                          · rw [houtEq, hresEq]
                          · rw [← hresEq, ← hs'Eq]
                            exact hrelOut

/-- `ShMemLoad` Local sub-case of HOL `compile_correct`.  HOL resumes the
    `ShMemLoad` case with a `Cases` on the `varkind` constructor
    (`pan_globalsProofScript.sml:757-...`); this piece fixes `vk = Local`, where
    the compiler keeps the constructor and only compiles the address.  The
    Global sub-case (the nested `Dec`/`Seq`/`Store` lowering) is tracked by a
    child of `flapjack-pxn.18.5.2.30`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_ShMemLoad_local {width : Nat} {σ : Type} [NeZero width]
    (operator : OpSize) (name : MlS) (address : ExpHOL width)
    (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.shMemLoad operator .local name address) = (res, s') ∧
        res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t
          (compileProgExactHOL ctxt (.shMemLoad operator .local name address)) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  intro res ctxt t s' ⟨hrel, hev, hne⟩
  have hcompile : compileProgExactHOL ctxt (.shMemLoad operator .local name address) =
      .shMemLoad operator .local name (compileExpExactHOL ctxt address) := by
    simp [compileProgExactHOL]
  rw [hcompile]
  rw [evaluateHOLFiniteState_shMemLoad_source] at hev
  rw [evaluateHOLFiniteState_shMemLoad_source]
  cases haddrS : (@evalHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) address) with
  | none =>
      simp only [haddrS] at hev
      exact absurd (Prod.mk.inj hev).1.symm hne
  | some av =>
      cases av with
      | rStruct fields =>
          simp only [haddrS] at hev
          exact absurd (Prod.mk.inj hev).1.symm hne
      | nStruct structName fields =>
          simp only [haddrS] at hev
          exact absurd (Prod.mk.inj hev).1.symm hne
      | val avp =>
          cases avp with
          | word addr =>
              have haddrT : @evalHOLFinite width σ _ t
                  (fun a => Classical.propDecidable (t.memaddrs a))
                  (compileExpExactHOL ctxt address) = some (.val (.word addr)) :=
                Flapjack.PanGlobalsCompileExpCorrect.compileExpCorrectHOL s address
                  (.val (.word addr)) ctxt t ⟨hrel, haddrS⟩
              cases hlook : (@lookupKvarHOLFinite width σ _ .local name s) with
              | none =>
                  simp only [haddrS, hlook] at hev
                  exact absurd (Prod.mk.inj hev).1.symm hne
              | some lv =>
                  cases lv with
                  | rStruct fields =>
                      simp only [haddrS, hlook] at hev
                      exact absurd (Prod.mk.inj hev).1.symm hne
                  | nStruct structName fields =>
                      simp only [haddrS, hlook] at hev
                      exact absurd (Prod.mk.inj hev).1.symm hne
                  | val lvp =>
                      cases lvp with
                      | word w =>
                          have hlookT : (@lookupKvarHOLFinite width σ _ .local name t) =
                              some (.val (.word w)) := by
                            unfold lookupKvarHOLFinite at hlook ⊢
                            rw [← hrel.2.1 rfl]
                            exact hlook
                          simp only [haddrS, haddrT, hlook, hlookT] at hev ⊢
                          obtain ⟨hresOut, hs'Out⟩ := Prod.mk.inj hev
                          obtain ⟨houtEq, hrelOut⟩ :=
                            shMemLoadLocalRelationHOL ctxt s t hrel name addr (nbOpHOL operator)
                          refine ⟨(shMemLoadFin t .local name addr
                            (nbOpHOL operator)).2, ?_, ?_⟩
                          · rw [houtEq, hresOut]
                          · rw [← hresOut, ← hs'Out]
                            exact hrelOut

end PanGlobalsCompileCorrect

end Flapjack
