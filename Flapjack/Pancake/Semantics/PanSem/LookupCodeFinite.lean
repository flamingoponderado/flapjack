import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack.PanSemStateFiniteExact
open Flapjack.Pancake.PanLang

/-- Canonical code-input and callee-local-output rendering of lookup_code.
The existing raw-input finite-result helper retains the original lookup,
ALL_DISTINCT, LIST_REL and ordered ZIP update clauses. This canonical input
entry point is not tagged while its heterogeneous-map qualifier review is
pending. The executed evaluator still uses the raw-input helper; routing and
the tagged declaration remain tracked on the parent bead. -/
def lookupCodeCanonicalHOL {width : Nat} [NeZero width]
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (arguments : List (ValueHOL width)) :
    Option (ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL) :=
  lookupCodeHOLFinite code.lookup fname arguments

/-- Unconditional input/output projection certificate against the independent
raw lookup operation. Both failure and successful structured callee maps are
covered; no success equation is assumed. This is representation infrastructure
with no independently named HOL declaration. -/
theorem holFmapAsFiniteSupportHeterogeneousFunctionWitness_lookupCodeCanonicalHOL
    {width : Nat} [NeZero width]
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (arguments : List (ValueHOL width)) :
    (lookupCodeCanonicalHOL code fname arguments).map
      (fun result => (result.1, result.2.1.lookup, result.2.2)) =
      lookupCodeHOLExact code.lookup fname arguments := by
  unfold lookupCodeCanonicalHOL lookupCodeHOLFinite
  split <;> simp_all

end Flapjack.PanSemStateFiniteExact
