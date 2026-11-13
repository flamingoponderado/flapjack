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

    The typed capture `exp_hdl_def_typed` (`pan_to_crep_typed_probe.out`)
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

/-- Codec from the production `String`-keyed finite map to the exact
    `MlString`-keyed finite-support carrier: names go through the total
    `MlString.ofString` (whose inverse is `toStringOfBytes`), shapes through
    `shapeToHOL`, and the flattened word lists are unchanged. The support
    premise is carried explicitly because the production map is a bare
    function. Flapjack-only representation bridge. -/
def finiteMapToHOLExact (fm : FiniteMap String (Shape × List Nat))
    (hsupport : ∃ keys : List String, ∀ key, fm key ≠ none → key ∈ keys) :
    HolFiniteMapExact MlS (ShapeHOL × List Nat) :=
  ⟨finiteMapToHOL fm, by
    obtain ⟨keys, hkeys⟩ := hsupport
    refine ⟨keys.map Flapjack.Basis.Pure.MlString.ofString, ?_⟩
    intro key hkey
    have hsource : fm (Flapjack.Basis.Pure.MlString.toStringOfBytes key) ≠ none := by
      simpa [finiteMapToHOL] using hkey
    exact List.mem_map.mpr
      ⟨_, hkeys _ hsource, Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes key⟩⟩

/-- Narrow kernel bridge: on every byte-ranged variable name, encoding the
    production finite map and running the tagged exact `expHdlExact` agrees with
    the `crepProgToHOL` image of the executed `expHdlFiniteMap`. The production
    helper remains the executed one; routing the executed handler setup through
    the exact carrier is tracked by `flapjack-pxn.18.3.5.8.13`. -/
theorem crepProgToHOL_expHdlFiniteMap {width : Nat} [NeZero width]
    (fm : FiniteMap String (Shape × List Nat)) (v : String)
    (hsupport : ∃ keys : List String, ∀ key, fm key ≠ none → key ∈ keys)
    (hv : ∀ c ∈ v.toList, c.toNat < 256) :
    crepProgToHOL (expHdlFiniteMap (α := BitVec width) fm v)
      = expHdlExact (width := width) (finiteMapToHOLExact fm hsupport)
          (Flapjack.Basis.Pure.MlString.ofString v) := by
  unfold expHdlFiniteMap expHdlExact finiteMapToHOLExact finiteMapToHOL
  simp only [FLOOKUP]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes v hv]
  cases h : fm v with
  | none => simp [crepProgToHOL]
  | some pair =>
      obtain ⟨shape, names⟩ := pair
      simp only [Option.map_some]
      rw [crepProgToHOL_crepNestedSeqHOL, panMap2_assign_map,
        crepExpMapToHOL_loadGlobals]

end Flapjack
