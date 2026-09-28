import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd
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

/-!
# `pc_compile_correct` over the exact carriers

The full HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`), assembled as in
HOL: `recInduct panSemTheory.evaluate_ind` (the tagged `evaluateIndHOL`) with the
21 tagged constructor cases of `PcCompileCorrect/<Case>.lean`, each proved with
HOL's printed `evaluate_ind` induction hypotheses and no extra premise.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)
open PanSemStateFiniteExact

namespace PcCompileCorrectAssemblyWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged assembled theorem below (delegating to the imported checked witnesses). -/

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

end PcCompileCorrectAssemblyWitnesses

/-- The HOL induction `recInduct panSemTheory.evaluate_ind` of
    `pc_compile_correct`: the tagged `evaluateIndHOL` with `P := pcCompileCorrectAtHOL`,
    discharged by the 21 tagged constructor cases `pcCompileCorrect_<Case>` (the
    `ExtCall` case is stated as `pcCompileCorrectAt` and converted by
    `pcCompileCorrectAt_iff_HOL`).  Untagged helper of `pcCompileCorrect`. -/
theorem pcCompileCorrect_all {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (s : PanSemStateFiniteExact width σ), pcCompileCorrectAtHOL p s := by
  intro p s
  refine evaluateIndHOL (fun ps : ProgHOL width × PanSemStateFiniteExact width σ =>
    pcCompileCorrectAtHOL ps.1 ps.2)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ p s
  all_goals first
    | exact pcCompileCorrect_Skip
    | exact pcCompileCorrect_Dec
    | exact pcCompileCorrect_Assign
    | exact pcCompileCorrect_Primitive
    | exact pcCompileCorrect_Store
    | exact pcCompileCorrect_Store32
    | exact pcCompileCorrect_StoreByte
    | exact pcCompileCorrect_ShMemLoad
    | exact pcCompileCorrect_ShMemStore
    | exact pcCompileCorrect_Seq
    | exact pcCompileCorrect_If
    | exact pcCompileCorrect_While
    | exact pcCompileCorrect_Break
    | exact pcCompileCorrect_Continue
    | exact pcCompileCorrect_Call
    | exact pcCompileCorrect_DecCall
    | exact pcCompileCorrect_ExtCall
    | exact pcCompileCorrect_Raise
    | exact pcCompileCorrect_Return
    | exact pcCompileCorrect_Tick
    | exact pcCompileCorrect_Annot

/-- HOL `pc_compile_correct` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`).
    The statement is HOL's: binders `v v1 res s1 t ctxt`, the conjunctive
    premise (`evaluate (v,v1) = (res,s1)`, `res ≠ SOME Error`, `state_rel`,
    `code_rel`, `excp_rel`, `locals_rel`, `localised_prog v`) and the existential
    target run with `state_rel`/`code_rel`/`excp_rel` and the inline
    `case res of`; the translation (tagged exact evaluators, compiler, relations,
    and the qualifiers below) is the one reviewed for the constructor cases.
    Proved by `pcCompileCorrect_all`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect {width : Nat} {σ : Type} [NeZero width] :
    ∀ (v : ProgHOL width) (v1 : PanSemStateFiniteExact width σ) (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      v1.evaluateHOLFiniteState v = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact v1 t ∧
        codeRelExactHOLW ctxt v1.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids v1.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt v1.locals t.locals ∧
        localisedProgHOL v = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt v) =
          (res1, t1) ∧
        panToCrepStateRelFiniteExact s1 t1 ∧ codeRelExactHOLW ctxt s1.code t1.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
        match res with
        | none => res1 = none ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some .error => False
        | some .timeOut => res1 = some .timeOut
        | some .break =>
            res1 = some (.break 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some .continue =>
            res1 = some (.continue 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some (.returned rv) => res1 = some (.return (flattenHOL rv))
        | some (.exception eid v') =>
            (match ctxt.eids.lookup eid with
             | none => False
             | some n =>
                 res1 = some (.exception n) ∧
                 (1 ≤ sizeOfShapeHOL (shapeOfHOLExact v') →
                   globalsLookupHOL t1 v' = some (flattenHOL v') ∧
                     sizeOfShapeHOL (shapeOfHOLExact v') ≤ 32))
        | some (.finalFfi f) => res1 = some (.finalFfi f) := by
  intro v v1 res s1 t ctxt h
  exact pcCompileCorrect_all v v1 res s1 t ctxt h

end Flapjack
