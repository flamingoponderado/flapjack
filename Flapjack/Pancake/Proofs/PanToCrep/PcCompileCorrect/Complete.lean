import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Annot
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assign
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Break
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Continue
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Dec
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.DecCall
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.ExtCall
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.If
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Primitive
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Raise
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Return
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Seq
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.ShMemLoad
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.ShMemStore
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Skip
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Store
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Store32
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.StoreByte
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Tick
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.While
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd

/-!
# Assembled HOL `pc_compile_correct` over the exact carriers

HOL `pc_compile_correct` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`)
is proved by `recInduct panSemTheory.evaluate_ind` (rebound at
`panSemScript.sml:777-778`), whose predicate is `P (v, v1)`. Its 21 constructor
cases are each proved against `pcCompileCorrectAt` in the sibling modules
(`Skip`, `Dec`, `Assign`, `Primitive`, `Store`, `Store32`, `StoreByte`,
`ShMemLoad`, `ShMemStore`, `Seq`, `If`, `Break`, `Continue`, `While`, `Return`,
`Raise`, `Tick`, `Annot`, `Call`, `DecCall`, `ExtCall`).

This module assembles them: it applies the exact tagged induction principle
`evaluateIndHOL` (the reviewed port of the rebound `panSem$evaluate_ind`) at the
motive `fun (pair : ProgHOL width × PanSemStateFiniteExact width σ) =>
pcCompileCorrectAt pair.1 pair.2`, discharging each of the 21 conjuncts with the
corresponding case lemma. The case lemmas take HOL's induction hypotheses as
explicit arguments in the shape of the rebound `evaluate_ind`; the small adapters
below convert the flattened conjunct form of `evaluateIndHOL` into the
arrow-shaped hypotheses the case lemmas expect. Nothing is added to the
statement: the assembled theorem is exactly `∀ program source,
pcCompileCorrectAt program source`, i.e. HOL's
`∀p s. P (p, s)` with the source run the tagged total
`evaluateHOLFiniteState`, the target run the tagged total
`evalCrepSemHOLProgExact`, and the compiler the tagged `compileProgExactHOLW`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL)

namespace PcCompileCorrectCompleteWitnesses

/-! Same-module canonical relation witnesses for the carriers qualified by the
assembled `pc_compile_correct` theorem. -/

theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact

theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_CrepSemHOLState state

end PcCompileCorrectCompleteWitnesses

/-- Assembled exact HOL `pc_compile_correct`
    (`pan_to_crepProofScript.sml:442-468`), from the tagged exact induction
    principle `evaluateIndHOL` and the 21 tagged constructor cases. The carrier
    qualifiers are the reviewed finite-map and positive-word translations;
    the same-module canonical witnesses are above. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect {width : Nat} {σ : Type} [NeZero width] :
    ∀ (program : ProgHOL width) (source : PanSemStateFiniteExact width σ),
      pcCompileCorrectAt program source := by
  intro program source
  exact evaluateIndHOL (width := width) (σ := σ)
    (P := fun pair : ProgHOL width × PanSemStateFiniteExact width σ =>
      pcCompileCorrectAt pair.1 pair.2)
    ⟨-- Skip
     fun s => pcCompileCorrectAt_skip s,
     -- Dec
     fun v sh e prog s ih =>
       pcCompileCorrectAt_dec v sh e prog s (fun value he hs => ih value ⟨he, hs⟩),
     -- Assign
     fun vk v src s => pcCompileCorrectAt_assign vk v src s,
     -- Primitive
     fun v pop es s => pcCompileCorrectAt_primitive v pop es s,
     -- Store
     fun dst src s => pcCompileCorrectAt_store dst src s,
     -- Store32
     fun dst src s => pcCompileCorrectAt_store32 dst src s,
     -- StoreByte
     fun dst src s => pcCompileCorrectAt_storeByte dst src s,
     -- ShMemLoad
     fun op vk v ad s => pcCompileCorrectAt_shMemLoad op vk v ad s,
     -- ShMemStore
     fun op ad e s => pcCompileCorrectAt_shMemStore op ad e s,
     -- Seq
     fun c1 c2 s ih =>
       pcCompileCorrectAt_seq c1 c2 s (fun res s1 he hn => ih.1 res s1 ⟨he.symm, hn⟩) ih.2,
     -- If
     fun e c1 c2 s ih =>
       pcCompileCorrectAt_ite e c1 c2 s (fun w he => ih (.val (.word w)) (.word w) w ⟨he, rfl, rfl⟩),
     -- Break
     fun s => pcCompileCorrectAt_break s,
     -- Continue
     fun s => pcCompileCorrectAt_continue s,
     -- While
     fun e c s ih =>
       pcCompileCorrectAt_while e c s
         (fun w s1 he hw hc hcont =>
           ih.1 (.val (.word w)) (.word w) w (some .continue) s1 .continue
             ⟨he, rfl, rfl, hw, hc, hcont.symm, rfl, rfl⟩)
         (fun w s1 he hw hc hnone =>
           ih.2.1 (.val (.word w)) (.word w) w none s1
             ⟨he, rfl, rfl, hw, hc, hnone.symm, rfl⟩)
         (fun w he hw hc => ih.2.2 (.val (.word w)) (.word w) w ⟨he, rfl, rfl, hw, hc⟩),
     -- Return
     fun e s => pcCompileCorrectAt_return s e,
     -- Raise
     fun eid e s => pcCompileCorrectAt_raise eid e s,
     -- Tick
     fun s => pcCompileCorrectAt_tick s,
     -- Annot
     fun v0 v1 s => pcCompileCorrectAt_annot v0 v1 s,
     -- Call
     fun caltyp fname argexps s ih =>
       pcCompileCorrectAt_call caltyp fname argexps s
         ⟨fun values prog newlocals returnShape st eid exn v1 evar p sh
             he hl hc hb hi hesh hshape hvalid =>
           ih.1 values (prog, newlocals, returnShape) prog (newlocals, returnShape)
             newlocals returnShape (some (.exception eid exn), st) (some (.exception eid exn))
             st (.exception eid exn) eid exn (v1, some (eid, evar, p)) v1
             (some (eid, evar, p)) (eid, evar, p) eid (evar, p) evar p sh
             ⟨he, hl, rfl, rfl, hc, hb.symm, rfl, rfl, rfl, hi, rfl, rfl, rfl, rfl, rfl,
               hesh, hshape, hvalid⟩,
          fun values prog newlocals returnShape he hl hc =>
           ih.2 values (prog, newlocals, returnShape) prog (newlocals, returnShape)
             newlocals returnShape ⟨he, hl, rfl, rfl, hc⟩⟩,
     -- DecCall
     fun rt shape fname argexps prog1 s ih =>
       pcCompileCorrectAt_decCall rt shape fname argexps prog1 s
         ⟨fun values prog newlocals returnShape st retv he hl hc hb hshape hret =>
           ih.1 values (prog, newlocals, returnShape) prog (newlocals, returnShape)
             newlocals returnShape (some (.returned retv), st) (some (.returned retv))
             st (.returned retv) retv
             ⟨he, hl, rfl, rfl, hc, hb.symm, rfl, rfl, rfl, hshape, hret⟩,
          fun values prog newlocals returnShape he hl hc =>
           ih.2 values (prog, newlocals, returnShape) prog (newlocals, returnShape)
             newlocals returnShape ⟨he, hl, rfl, rfl, hc⟩⟩,
     -- ExtCall
     fun ffi_index ptr1 len1 ptr2 len2 s =>
       pcCompileCorrect_ExtCall ffi_index ptr1 len1 ptr2 len2 s⟩
    program source

end Flapjack
