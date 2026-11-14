module

public import Flapjack.Pancake.CrepToLoop
public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

/-!
# Exact `crep_to_loopScript.sml` `rt_vars_def`

The production helper `rtVars` in `CrepToLoop.lean` uses the raw lookup-function
map `FiniteMap κ Nat` (infinite support admitted). This module ports HOL
`rt_vars_def` over the reviewed canonical finite-map carrier
`HolFiniteMapExact`, which is the `|->` translation used by the exact Crep and
PanSem carriers.
-/

namespace Flapjack

/-- Broad lookup projection for the parameter witness roundtrip. Flapjack
    infrastructure; it has no separate HOL original. -/
def rtVarsMaptoBroad_lookup {α : Type} (fm : HolFiniteMapExact α Nat) : α → Option Nat :=
  fm.lookup

/-- Reconstruct the canonical carrier from a broad lookup and support proof. -/
def rtVarsMapofBroad {α : Type} (lookup : α → Option Nat)
    (finiteSupport : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact α Nat := ⟨lookup, finiteSupport⟩

/-- Canonical standalone-map witness for the exact `rt_vars_def` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_rtVarsHOL_fm {α : Type}
    (fm : HolFiniteMapExact α Nat) :
    rtVarsMapofBroad (rtVarsMaptoBroad_lookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Exact port of HOL `rt_vars_def` (`cakeml/pancake/crep_to_loopScript.sml:113-118`):

```
rt_vars fm vs (mx:num) =
  case OPT_MMAP (FLOOKUP fm) vs of
   | NONE => [mx+1]
   | SOME m => m
```

The typed HOL capture is `scripts/hol-probes/crep_to_loop_rt_vars_typed_probe.out`:
`∀ (fm : α |-> num) (vs : α list) (mx : num). rt_vars fm vs mx = case OPT_MMAP
(FLOOKUP fm) vs of NONE => [mx + 1] | SOME m => m`. The finite map `α |-> num`
is the reviewed `HolFiniteMapExact α Nat` translation, `FLOOKUP` is `.lookup`,
and `OPT_MMAP` is `List.mapM` (the tagged `optMmapEqSome` records that
correspondence). No quantifier, hypothesis, or side condition is added. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "rt_vars_def"
  (fmap_as_finite_support_parameters := [fm])]
def rtVarsHOL {α : Type} (fm : HolFiniteMapExact α Nat) (vs : List α) (mx : Nat) :
    List Nat :=
  match vs.mapM (fun v => fm.lookup v) with
  | none => [mx + 1]
  | some m => m

end Flapjack
