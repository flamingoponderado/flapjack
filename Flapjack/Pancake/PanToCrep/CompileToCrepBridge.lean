import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.PanToCrep.CompileProg

/-!
Byte-ranged bridge between the production declaration-only compiler
`compileToCrepHOL` and the tagged exact `compileToCrepExactHOLW`
(bead flapjack-tlht).  Flapjack-specific infrastructure: no HOL original,
so no `@[hol]` tag; the transport codecs are documented beside each lemma.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Encode a production `(params, return)` function signature to exact carriers. -/
def encodeFuncValue (v : List (VarName × Shape) × Shape) :
    List (MlS × ShapeHOL) × ShapeHOL :=
  (v.1.map paramToHOL, shapeToHOL v.2)

/-- Decode an exact `(params, return)` function signature to production carriers. -/
def decodeFuncValue (v : List (MlS × ShapeHOL) × ShapeHOL) :
    List (VarName × Shape) × Shape :=
  (v.1.map paramOfHOL, shapeOfHOL v.2)

@[simp] theorem encodeFuncValue_decodeFuncValue
    (v : List (MlS × ShapeHOL) × ShapeHOL) :
    encodeFuncValue (decodeFuncValue v) = v := by
  obtain ⟨p, r⟩ := v
  simp [encodeFuncValue, decodeFuncValue, List.map_map, Function.comp_def]

theorem holFiniteMapExact_ext {α β : Type}
    {left right : HolFiniteMapExact α β}
    (h : ∀ key, left.lookup key = right.lookup key) : left = right := by
  cases left with
  | mk l hl =>
    cases right with
    | mk r hr =>
      have heq : l = r := funext h
      subst r
      rfl

/-! ### Local copies of the private `make_vmap` bridge

`CompileProg.lean` proves the exact/production parameter-allocation agreement as
`private` declarations, so the declaration-only assembled bridge below restates
them here. -/

theorem ofString_injective_on_ranged_names_bridge {left right : String}
    (hleft : Flapjack.Pancake.PanLang.NameRanged left)
    (hright : Flapjack.Pancake.PanLang.NameRanged right)
    (h : Flapjack.Basis.Pure.MlString.ofString left =
      Flapjack.Basis.Pure.MlString.ofString right) : left = right := by
  have hdecoded := congrArg Flapjack.Basis.Pure.MlString.toStringOfBytes h
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes left hleft,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes right hright]
    at hdecoded
  exact hdecoded

theorem fupdateList_ofString_bridge {β γ : Type}
    (decode : β → γ) (entries : List (String × β))
    (hranged : ∀ entry ∈ entries, Flapjack.Pancake.PanLang.NameRanged entry.1)
    (lookupExact : Flapjack.Basis.Pure.MlString.MlString → Option γ)
    (lookupProduction : String → Option β)
    (hbase : ∀ key,
      lookupExact key = (lookupProduction
        (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map decode) :
    ∀ key,
      Flapjack.FUPDATE_LIST lookupExact
          (entries.map (fun entry =>
            (Flapjack.Basis.Pure.MlString.ofString entry.1, decode entry.2))) key =
        (Flapjack.FUPDATE_LIST lookupProduction entries
          (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map decode := by
  induction entries generalizing lookupExact lookupProduction with
  | nil =>
      intro key
      simpa [Flapjack.FUPDATE_LIST_nil] using hbase key
  | cons entry entries ih =>
      obtain ⟨name, value⟩ := entry
      have hname : Flapjack.Pancake.PanLang.NameRanged name :=
        hranged (name, value) (by simp)
      have htail : ∀ entry ∈ entries,
          Flapjack.Pancake.PanLang.NameRanged entry.1 := by
        intro item hitem
        exact hranged item (by simp [hitem])
      have hupdated : ∀ key,
          Flapjack.FUPDATE lookupExact
              (Flapjack.Basis.Pure.MlString.ofString name, decode value) key =
            (Flapjack.FUPDATE lookupProduction (name, value)
              (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map decode := by
        intro key
        have hkey : Flapjack.Pancake.PanLang.NameRanged
            (Flapjack.Basis.Pure.MlString.toStringOfBytes key) :=
          PanToCrepContextExact.toProduction_key_nameRanged key
        by_cases heq : name = Flapjack.Basis.Pure.MlString.toStringOfBytes key
        · have heq' : Flapjack.Basis.Pure.MlString.ofString name = key := by
            rw [heq, Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
          have hprod : (name == Flapjack.Basis.Pure.MlString.toStringOfBytes key) = true :=
            beq_iff_eq.mpr heq
          have hexact : (Flapjack.Basis.Pure.MlString.ofString name == key) = true :=
            beq_iff_eq.mpr heq'
          simp [Flapjack.FUPDATE, hprod, hexact]
        · have hne : Flapjack.Basis.Pure.MlString.ofString name ≠ key := by
            intro hml
            have hml' : Flapjack.Basis.Pure.MlString.ofString name =
                Flapjack.Basis.Pure.MlString.ofString
                  (Flapjack.Basis.Pure.MlString.toStringOfBytes key) := by
              rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
              exact hml
            exact heq (ofString_injective_on_ranged_names_bridge hname hkey hml')
          have hprod : (name == Flapjack.Basis.Pure.MlString.toStringOfBytes key) = false :=
            beq_eq_false_iff_ne.mpr heq
          have hexact : (Flapjack.Basis.Pure.MlString.ofString name == key) = false :=
            beq_eq_false_iff_ne.mpr hne
          simp [Flapjack.FUPDATE, hprod, hexact, hbase key]
      intro key
      simpa only [List.map_cons, Flapjack.FUPDATE_LIST_cons] using
        ih htail (Flapjack.FUPDATE lookupExact
          (Flapjack.Basis.Pure.MlString.ofString name, decode value))
          (Flapjack.FUPDATE lookupProduction (name, value)) hupdated key

def panToCrepShapeSlotsExact_bridge :
    List ShapeHOL → Nat → List (List Nat)
  | [], _ => []
  | shape :: shapes, offset =>
      (List.range (sizeOfShapeHOL shape)).map (offset + ·) ::
        panToCrepShapeSlotsExact_bridge shapes (offset + sizeOfShapeHOL shape)

def panToCrepParamsVmapEntriesOffset_bridge :
    List (VarName × Shape) → Nat → List (MlS × (ShapeHOL × List Nat))
  | [], _ => []
  | (name, shape) :: params, offset =>
      (Flapjack.Basis.Pure.MlString.ofString name,
        (shapeToHOL shape,
          (List.range (sizeOfShapeHOL (shapeToHOL shape))).map (offset + ·))) ::
        panToCrepParamsVmapEntriesOffset_bridge params
          (offset + Shape.shapeSize shape)

end Flapjack
