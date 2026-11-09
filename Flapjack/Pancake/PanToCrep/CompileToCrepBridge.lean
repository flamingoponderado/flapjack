module

public import Flapjack.Pancake.PanToCrep.CompileExact
public import Flapjack.Pancake.PanToCrep.CompileProg

@[expose] public section

/-!
Byte-ranged bridge between the production declaration-only compiler
`compileToCrepHOL` and the tagged exact `compileToCrepExactHOLW`
(bead flapjack-tlht).  Flapjack-specific infrastructure: no HOL original,
so no `@[hol]` tag; the transport codecs are documented beside each lemma.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- The right-fold association-list rendering of HOL `alist_to_fmap` equals the
    left fold of `FUPDATE` over the reversed association list. -/
theorem alistToFmap_eq_fupdate_list_reverse [BEq α] (entries : List (α × β)) :
    alistToFmap entries = FUPDATE_LIST FEMPTY entries.reverse := by
  induction entries with
  | nil => simp [alistToFmap, FUPDATE_LIST]
  | cons entry entries ih =>
    obtain ⟨k, v⟩ := entry
    change FUPDATE (alistToFmap entries) (k, v) =
      FUPDATE_LIST FEMPTY ((k, v) :: entries).reverse
    rw [ih, List.reverse_cons, FUPDATE_LIST_append]
    rfl

/-- Lookup-level correspondence between `alistToFmap`s of two association lists
    whose entries are related by a key encoder `f` and a value encoder `h`, with
    `decode` a left inverse of `h` on the entries.  The key encoder must be
    injective at the queried key, which is what makes the first-binding
    (duplicate) semantics line up. -/
theorem flookup_alistToFmap_map_decode {α β γ δ : Type}
    [BEq α] [LawfulBEq α] [BEq γ] [LawfulBEq γ]
    (f : α → γ) (h : β → δ) (decode : δ → β)
    (entries : List (α × β)) (key : α)
    (hinj : ∀ e ∈ entries, f e.1 = f key → e.1 = key)
    (hleft : ∀ e ∈ entries, decode (h e.2) = e.2) :
    (FLOOKUP (alistToFmap (entries.map (fun e => (f e.1, h e.2)))) (f key)).map decode =
      FLOOKUP (alistToFmap entries) key := by
  induction entries with
  | nil => simp [alistToFmap]
  | cons entry entries ih =>
    obtain ⟨k, v⟩ := entry
    have htail_inj : ∀ e ∈ entries, f e.1 = f key → e.1 = key :=
      fun e he => hinj e (by simp [he])
    have htail_left : ∀ e ∈ entries, decode (h e.2) = e.2 :=
      fun e he => hleft e (by simp [he])
    have hhead_left : decode (h v) = v := hleft (k, v) (by simp)
    have hmap : ((k, v) :: entries).map (fun e => (f e.1, h e.2)) =
        (f k, h v) :: entries.map (fun e => (f e.1, h e.2)) := rfl
    rw [hmap, alistToFmap, alistToFmap, List.foldr_cons, List.foldr_cons]
    cases hkk : (k == key) with
    | true =>
        have hkeq : k = key := beq_iff_eq.mp hkk
        have hfk : (f k == f key) = true := by rw [hkeq, beq_self_eq_true]
        rw [FLOOKUP_update, FLOOKUP_update, hkk, hfk]
        simp [hhead_left]
    | false =>
        have hkne : k ≠ key := beq_eq_false_iff_ne.mp hkk
        have hfkne : ¬ (f k = f key) := by
          intro hfe
          exact hkne (hinj (k, v) (by simp) hfe)
        have hfk : (f k == f key) = false := beq_eq_false_iff_ne.mpr hfkne
        rw [FLOOKUP_update, FLOOKUP_update, hkk, hfk]
        exact ih htail_inj htail_left

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

/-- Zipping a mapped list with codes of the mapped length equals mapping the
    code-zipped original. -/
theorem zip_map_fst {α β : Type} (f : α → String) (x : List α) (g : Nat → β) :
    (x.map f).zip ((List.range (x.map f).length).map g) =
      (x.zip ((List.range x.length).map g)).map (fun e => (f e.1, e.2)) := by
  rw [List.length_map, List.zip_map_left]
  rfl

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

theorem panToCrepContextExact_ext {width : Nat} [NeZero width]
    {a b : PanToCrepContextExact width}
    (hvars : a.vars = b.vars) (hfuncs : a.funcs = b.funcs)
    (heids : a.eids = b.eids) (hvmax : a.vmax = b.vmax) : a = b := by
  cases a
  cases b
  simp_all

/-- The exact `crep_vars` of a parameter list encoded by `paramToHOL` is the
    production `panToCrepVars` slot list. -/
theorem crepVarsHOL_map_paramToHOL (l : List (FunName × Shape)) :
    crepVarsHOL (l.map paramToHOL) = panToCrepVars l := by
  simp [crepVarsHOL, panToCrepVars, paramToHOL, List.map_map, Function.comp_def]

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

theorem withShapeHOL_range_offset_bridge (shapes : List ShapeHOL) (offset : Nat) :
    withShapeHOL shapes
        ((List.range (sizeOfShapeHOL (.comb shapes))).map (offset + ·)) =
      panToCrepShapeSlotsExact_bridge shapes offset := by
  induction shapes generalizing offset with
  | nil => simp [withShapeHOL, panToCrepShapeSlotsExact_bridge]
  | cons shape shapes ih =>
      simp only [withShapeHOL, panToCrepShapeSlotsExact_bridge, sizeOfShapeHOL,
        sizeOfShapesHOL]
      rw [List.range_add]
      have htail := ih (offset + sizeOfShapeHOL shape)
      simpa [sizeOfShapeHOL, sizeOfShapesHOL, Nat.add_assoc,
        Function.comp_def] using htail

def panToCrepParamsVmapEntriesOffset_bridge :
    List (VarName × Shape) → Nat → List (MlS × (ShapeHOL × List Nat))
  | [], _ => []
  | (name, shape) :: params, offset =>
      (Flapjack.Basis.Pure.MlString.ofString name,
        (shapeToHOL shape,
          (List.range (sizeOfShapeHOL (shapeToHOL shape))).map (offset + ·))) ::
        panToCrepParamsVmapEntriesOffset_bridge params
          (offset + Shape.shapeSize shape)

theorem compileParamVars_vmap_entries_bridge (params : List (VarName × Shape))
    (offset : Nat) :
    (compileParamVars params offset).1.map (fun entry =>
      (Flapjack.Basis.Pure.MlString.ofString entry.1,
        (shapeToHOL entry.2.1, entry.2.2))) =
      panToCrepParamsVmapEntriesOffset_bridge params offset := by
  induction params generalizing offset with
  | nil => simp [compileParamVars, panToCrepParamsVmapEntriesOffset_bridge]
  | cons parameter params ih =>
      cases parameter with
      | mk name shape =>
          simp [compileParamVars, panToCrepParamsVmapEntriesOffset_bridge,
            sizeOfShapeHOL_shapeToHOL, ih]

theorem panToCrepParamsVmapEntries_exact_offset_bridge
    (params : List (VarName × Shape)) (offset : Nat) :
    panToCrepParamsVmapEntriesOffset_bridge params offset =
      let exactParams := params.map fun (name, shape) =>
        (Flapjack.Basis.Pure.MlString.ofString name, shapeToHOL shape)
      let shapes := exactParams.map Prod.snd
      (exactParams.map Prod.fst).zip
        (shapes.zip (withShapeHOL shapes
          ((List.range (sizeOfShapeHOL (.comb shapes))).map (offset + ·)))) := by
  induction params generalizing offset with
  | nil => simp [panToCrepParamsVmapEntriesOffset_bridge]
  | cons parameter params ih =>
      cases parameter with
      | mk name shape =>
          simp only [panToCrepParamsVmapEntriesOffset_bridge, List.map_cons]
          rw [withShapeHOL_range_offset_bridge]
          simp only [panToCrepShapeSlotsExact_bridge, List.zip_cons_cons]
          have htail := ih (offset + Shape.shapeSize shape)
          dsimp at htail
          rw [withShapeHOL_range_offset_bridge] at htail
          simpa [sizeOfShapeHOL_shapeToHOL] using htail

theorem panToCrepMakeVmapHOLExactOfProductionParams_bridge
    (params : List (VarName × Shape))
    (hparams : ∀ p ∈ params,
      Flapjack.Pancake.PanLang.NameRanged p.1 ∧
        Flapjack.Pancake.PanLang.ShapeByteRanged p.2)
    (key : Flapjack.Basis.Pure.MlString.MlString) :
    (panToCrepMakeVmapHOLExact (params.map fun (name, shape) =>
      (Flapjack.Basis.Pure.MlString.ofString name,
        Flapjack.Pancake.PanLang.shapeToHOL shape))).lookup key =
      (panToCrepMakeVmapHOL params
        (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map
          (fun value => (Flapjack.Pancake.PanLang.shapeToHOL value.1, value.2)) := by
  let exactParams := params.map fun (name, shape) =>
    (Flapjack.Basis.Pure.MlString.ofString name,
      Flapjack.Pancake.PanLang.shapeToHOL shape)
  have hranged : ∀ entry ∈ (compileParamVars params 0).1,
      Flapjack.Pancake.PanLang.NameRanged entry.1 :=
    compileParamVars_entries_nameRanged params 0 (fun p hp => (hparams p hp).1)
  have hentries :
      ((compileParamVars params 0).1.map fun entry =>
        (Flapjack.Basis.Pure.MlString.ofString entry.1,
          (Flapjack.Pancake.PanLang.shapeToHOL entry.2.1, entry.2.2))) =
        (exactParams.map Prod.fst).zip
          ((exactParams.map Prod.snd).zip
            (Flapjack.Pancake.PanLang.withShapeHOL (exactParams.map Prod.snd)
              (List.range (Flapjack.Pancake.PanLang.sizeOfShapeHOL
                (.comb (exactParams.map Prod.snd)))))) := by
    calc
      _ = panToCrepParamsVmapEntriesOffset_bridge params 0 :=
        compileParamVars_vmap_entries_bridge params 0
      _ = _ := by
        simpa [exactParams, Function.comp_def] using
          panToCrepParamsVmapEntries_exact_offset_bridge params 0
  have hupdate := fupdateList_ofString_bridge
    (β := Shape × List Nat)
    (γ := Flapjack.Pancake.PanLang.ShapeHOL × List Nat)
    (fun value => (Flapjack.Pancake.PanLang.shapeToHOL value.1, value.2))
    (compileParamVars params 0).1
    (fun entry hentry => hranged entry hentry)
    (fun _ => none)
    FEMPTY
    (by intro query; rfl)
    key
  rw [Flapjack.holFmapAsFiniteSupportResultWitness_panToCrepMakeVmapHOLExact]
  simpa [exactParams, FEMPTY, panToCrepMakeVmapHOL,
    panToCrepMakeVmapRaw, hentries] using hupdate

end Flapjack
