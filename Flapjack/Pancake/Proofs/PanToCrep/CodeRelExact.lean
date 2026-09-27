import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.PanToCrep.CompileExact

/-!
Exact-carrier code relation for the HOL Pancake-to-Crep correctness boundary.
This lives below the counterpart proof module because it complements
`codeRelW` without changing that production-carrier relation.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-! HOL `code_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32-43`)
    quantifies a source map, a target map, and an arbitrary HOL compiler
    context. This definition mirrors those clauses directly over the exact
    carriers: `MlS`, `ShapeHOL`, `ProgHOL`, `CrepProgHOL`, and
    `PanToCrepContextExact`. Its body compiles every function in the supplied
    context with `compileProgExactHOLW`; it does not assume the context came
    from declarations or a production String map.

    It is deliberately UNTAGGED. `HolFiniteMapExact` is the reviewed canonical
    finite-support representation, but HOL's `sourceCode` and `targetCode` are
    independent map parameters rather than fields of one owning structure in
    this module. The current `(fmap_as_finite_support := [...])` qualifier
    only accepts named fields of one such carrier structure. Bundling these
    quantified maps just to satisfy that checker would change the theorem's
    binder shape, while using raw function maps would admit infinite supports.
    Keep `code_rel_def` untagged until the checker has a reviewed parameter-map
    qualifier or another faithful correspondence is approved. This is
    Flapjack-specific exact-carrier infrastructure, not a claimed HOL port.
-/
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

end Flapjack
