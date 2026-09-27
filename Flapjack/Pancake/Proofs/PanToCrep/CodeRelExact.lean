import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.PanToCrep.CompileExact

/-!
Exact-carrier code relation for the HOL Pancake-to-Crep correctness boundary.
This lives below the counterpart proof module because it complements
`codeRelW` without changing that production-carrier relation.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-! Exact source review of HOL `code_rel_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32-43`). HOL's three
    explicit arguments are `ctxt`, `s_code`, and `t_code`; inside the relation
    it universally quantifies `f`, `vshs`, `prog`, and `rsh` in that order.
    This definition preserves that binder structure and each clause:

    * a successful source `FLOOKUP` requires `localised_prog prog`;
    * `ctxt.funcs` must map `f` to the same `(vshs, rsh)`;
    * `vs` and `shs` are `MAP FST`/`MAP SND` of `vshs`, and `ns` is
      `GENLIST I (size_of_shape (Comb shs))`;
    * `nctxt` is exactly `ctxt_fc ctxt.funcs ctxt.eids vs shs ns`;
    * target lookup must return `(ns, compile nctxt prog)`.

    The carrier comparison is constructor-for-constructor: HOL `mlstring` is
    `MlS`, HOL `shape`/`prog`/`crepLang$prog` are `ShapeHOL`/`ProgHOL`/
    `CrepProgHOL`, and HOL's word type is the positive-width `BitVec width`.
    HOL finite-map parameters `s_code` and `t_code` use the canonical
    `HolFiniteMapExact` carrier, recorded as bare entries in
    `fmap_as_finite_support_relation`; the context's `funcs` and `eids` fields
    use the same representation and are named with their owner. No binder is
    bundled, no raw function map admits infinite support, and no key or
    executable behavior is changed. The canonical context roundtrip witness
    below validates that carrier field translation.

    This is an exact port of the HOL definition, not a theorem establishing
    `pc_compile_correct` and not evidence that the production String-backed
    compiler path uses this exact carrier. That executable-path replacement
    remains tracked on the parent correctness bead.
-/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_def"
  (fmap_as_finite_support_relation := [sourceCode, targetCode,
    PanToCrepContextExact.funcs, PanToCrepContextExact.eids])]
def codeRelExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceCode : HolFiniteMapExact MlS
      (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (targetCode : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) : Prop :=
  ∀ function variableShapes program returnShape,
    sourceCode.lookup function = some (variableShapes, program, returnShape) →
      localisedProgHOL program = true ∧
      context.funcs.lookup function = some (variableShapes, returnShape) ∧
      let variables := variableShapes.map Prod.fst
      let shapes := variableShapes.map Prod.snd
      let names := List.range (sizeOfShapeHOL (.comb shapes))
      let nextContext := ctxtFcExactHOL context.funcs context.eids variables shapes names
      targetCode.lookup function = some
        (names, compileProgExactHOLW nextContext program)

/-- Same-module finite-map relation witness for the imported exact context
    fields named by `codeRelExactHOLW`'s qualifier. Flapjack representation
    infrastructure only; the parameter maps are validated directly at their
    `HolFiniteMapExact` binders, so they need no owner witness. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context := by
  exact PanToCrepContextExact.holFmapAsFiniteSupportWitness context

end Flapjack
