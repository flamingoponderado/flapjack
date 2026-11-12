module

public import Flapjack.Pancake.PanToCrep
public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Exact finite-map port of `pan_to_crep$exp_hdl`, preserving the standalone HOL
map input binder. The parameter qualifier records its canonical
`HolFiniteMapExact` translation and checked lookup/support roundtrip.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL)

private def expHdlMaptoBroadlookup {α γ : Type}
    (fm : HolFiniteMapExact α (γ × List Nat)) :
    α → Option (γ × List Nat) := fm.lookup

private def expHdlMapofBroad {α γ : Type} (fm : α → Option (γ × List Nat))
    (support : ∃ keys : List α, ∀ key, fm key ≠ none → key ∈ keys) :
    HolFiniteMapExact α (γ × List Nat) := ⟨fm, support⟩

/-- Canonical map-parameter witness for `expHdlExact.fm`: the direct
    `HolFiniteMapExact` input roundtrips through its lookup and support proof. -/
theorem holFmapAsFiniteSupportParamWitness_expHdlExact_fm {α γ : Type}
    (fm : HolFiniteMapExact α (γ × List Nat)) :
    expHdlMapofBroad (expHdlMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Cake's `exp_hdl` over the exact finite-map carrier.

    HOL (`cakeml/pancake/pan_to_crepScript.sml:106-112`) is
    `exp_hdl fm v = case FLOOKUP fm v of
      | NONE => Skip
      | SOME (vshp, ns) => nested_seq (MAP2 Assign ns (load_globals 0w (LENGTH ns)))`.
    Here `vshp` is discarded, `FLOOKUP` reads `fm.lookup`,
    `nested_seq` is `crepNestedSeqHOL`, `MAP2 Assign` is `panMap2`, and
    `load_globals 0w n` is `loadGlobalsHOL 0w n`. The `LoadGlob` address is a
    fixed 5-bit word in HOL and Lean; the program word parameter is translated
    by `CrepProgHOL width` and `[NeZero width]`.

    The typed capture `exp_hdl_def_typed` (`pan_to_crep_proof_typed_probe.out`)
    types the map as `fm :β |-> γ # num list`: the key β, the discarded shape
    component γ and the program payload are independent HOL type variables.
    `vshp` is never used, so γ is arbitrary and the port keeps it generic as
    `{γ : Type}` (task 151); callers instantiate γ = ShapeHOL, the source
    shape carrier. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "exp_hdl_def"
  (fmap_as_finite_support_parameters := [fm])
  (words_as_type_indexed_bitvec)]
def expHdlExact {α γ : Type} {width : Nat} [NeZero width]
    (fm : HolFiniteMapExact α (γ × List Nat))
    (v : α) : CrepProgHOL width :=
  match fm.lookup v with
  | none => .skip
  | some (_, names) =>
      crepNestedSeqHOL
        (panMap2 (fun destination source => .assign destination source)
          names (loadGlobalsHOL (0 : BitVec 5) names.length))

/-- Consumer bridge to the raw-map helper; its support premise is exactly the
    finite-domain condition carried intrinsically by `HolFiniteMapExact`. -/
theorem expHdlExact_eq_expHdlHOL {width : Nat} [NeZero width]
    (fm : HolFiniteMapExact MlS (ShapeHOL × List Nat)) (v : MlS) :
    expHdlExact (width := width) fm v = expHdlHOL fm.lookup v := by
  cases hlookup : fm.lookup v <;> simp [expHdlExact, expHdlHOL, FLOOKUP, hlookup]

end Flapjack
