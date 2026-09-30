/- Negative scanner fixture: a kernel-valid theorem with an inherited premise
that assumes a false correspondence. This is not a HOL port or production code.
The two operations return different results; the theorem is valid only because
Lean adds the ambient `h` to its elaborated binders. -/
import Flapjack.FiniteMap

namespace Flapjack.HeterogeneousReviewProbe
abbrev MlS := Nat
abbrev CodeEntry := Bool
abbrev Value := Nat
abbrev Prog := Nat
abbrev Shape := Nat
def lookupCodeHOLFiniteExact (code : HolFiniteMapExact MlS CodeEntry)
    (fname : MlS) (arguments : List Value) :
    Option (Prog × HolFiniteMapExact MlS Value × Shape) :=
  let _ := (code, fname, arguments)
  none
def lookupCodeHOLExact (_code : MlS → Option CodeEntry)
    (_fname : MlS) (_arguments : List Value) :
    Option (Prog × (MlS → Option Value) × Shape) := some (0, fun _ => some 0, 0)
variable {h : ∀ (code : HolFiniteMapExact MlS CodeEntry) (fname : MlS) (arguments : List Value), (lookupCodeHOLFiniteExact code fname arguments).map (fun (body, locals, shape) => (body, locals.lookup, shape)) = lookupCodeHOLExact code.lookup fname arguments}
include h
theorem holFmapAsFiniteSupportHeterogeneousFunctionWitness_lookupCodeHOLFiniteExact
    (code : HolFiniteMapExact MlS CodeEntry) (fname : MlS) (arguments : List Value) :
    (lookupCodeHOLFiniteExact code fname arguments).map
      (fun (body, locals, shape) => (body, locals.lookup, shape)) =
      lookupCodeHOLExact code.lookup fname arguments := h code fname arguments

#print Flapjack.HeterogeneousReviewProbe.holFmapAsFiniteSupportHeterogeneousFunctionWitness_lookupCodeHOLFiniteExact
end Flapjack.HeterogeneousReviewProbe
