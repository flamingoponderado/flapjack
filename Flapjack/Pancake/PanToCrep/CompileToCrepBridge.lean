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

/-- Transport of one production `functionEntries` entry to the exact
    `functionsHOL` entry carrier. -/
def funEntryToHOL {width : Nat} [NeZero width]
    (e : FunName × List (VarName × Shape) × Prog (BitVec width) × Shape) :
    MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL :=
  (ofString e.1, e.2.1.map paramToHOL, progToHOL e.2.2.1, shapeToHOL e.2.2.2)

/-- The exact `functionsHOL` of the encoded declarations is the encoded
    production `functionEntries`. -/
theorem functionsHOL_map_declToHOL {width : Nat} [NeZero width]
    (ds : List (Decl (BitVec width))) :
    functionsHOL (ds.map declToHOL) = (functionEntries ds).map funEntryToHOL := by
  induction ds with
  | nil => simp [functionsHOL, functionEntries]
  | cons d ds ih =>
    cases d <;>
      simp [functionsHOL, functionEntries, declToHOL, funDeclToHOL, funEntryToHOL, ih]

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

/-- Production association-list entries of HOL `make_funcs`. -/
def prodFuncEntries {width : Nat} [NeZero width] (ds : List (Decl (BitVec width))) :
    List (FunName × (List (VarName × Shape) × Shape)) :=
  (functionEntries ds).map (fun e => (e.1, (e.2.1, e.2.2.2)))

/-- Production association-list entries of HOL `get_eids_from_decls`. -/
def prodEidsEntries {width : Nat} [NeZero width] (ds : List (Decl (BitVec width))) :
    List (String × BitVec width) :=
  let names := (exceptionEntries ds).map Prod.fst
  names.zip ((List.range names.length).map (BitVec.ofNat width))

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

/-- The exact `make_funcs` association list of the encoded declarations is the
    encoded production `make_funcs` association list. -/
theorem makeFuncsEntriesHOL_map_declToHOL {width : Nat} [NeZero width]
    (ds : List (Decl (BitVec width))) :
    makeFuncsEntriesHOL (functionsHOL (ds.map declToHOL)) =
      (prodFuncEntries ds).map (fun e => (ofString e.1, encodeFuncValue e.2)) := by
  rw [makeFuncsEntriesHOL, functionsHOL_map_declToHOL, prodFuncEntries, List.map_map]
  simp only [List.map_map]
  apply List.map_congr_left
  intro e _
  simp [funEntryToHOL, encodeFuncValue]

/-- Zipping a mapped list with codes of the mapped length equals mapping the
    code-zipped original. -/
theorem zip_map_fst {α β : Type} (f : α → String) (x : List α) (g : Nat → β) :
    (x.map f).zip ((List.range (x.map f).length).map g) =
      (x.zip ((List.range x.length).map g)).map (fun e => (f e.1, e.2)) := by
  rw [List.length_map, List.zip_map_left]
  rfl

/-- Reverse direction of `makeFuncsEntriesHOL_map_declToHOL`, valid on
    byte-ranged declarations: the production `make_funcs` association list is
    the decoded exact list. -/
theorem prodFuncEntries_eq_map {width : Nat} [NeZero width]
    (ds : List (Decl (BitVec width)))
    (hdecls : ∀ d ∈ ds, DeclByteRanged d) :
    prodFuncEntries ds =
      (makeFuncsEntriesHOL (functionsHOL (ds.map declToHOL))).map
        (fun e => (toStringOfBytes e.1, decodeFuncValue e.2)) := by
  rw [makeFuncsEntriesHOL_map_declToHOL, prodFuncEntries, List.map_map, List.map_map]
  apply List.map_congr_left
  intro src hsrc
  obtain ⟨hname, hparams, hret, _⟩ := functionEntries_byteRanged ds hdecls src hsrc
  have hparams' : ListParamByteRanged src.2.1 := fun p hp => hparams p hp
  have hval : decodeFuncValue (encodeFuncValue (src.2.1, src.2.2.2)) =
      (src.2.1, src.2.2.2) := by
    simp only [encodeFuncValue, decodeFuncValue]
    rw [List.map_map, listParamOfHOL_paramToHOL _ hparams',
      shapeOfHOL_shapeToHOL _ hret]
  simp only [Function.comp_apply]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes src.1 hname, hval]

/-- The production exception-id association entries are the decoded exact
    `get_eids_from_decls` entries. -/
theorem prodEidsEntries_eq_map {width : Nat} [NeZero width]
    (ds : List (Decl (BitVec width)))
    (hdecls : ∀ d ∈ ds, DeclByteRanged d) :
    prodEidsEntries ds =
      (getEidsEntriesHOL (ds.map declToHOL)).map
        (fun e => (toStringOfBytes e.1, e.2)) := by
  unfold prodEidsEntries getEidsEntriesHOL
  have hnames :
      ((exceptionsHOL (ds.map declToHOL)).map Prod.fst).map toStringOfBytes =
        (exceptionEntries ds).map Prod.fst := by
    have h := exceptionsHOL_map_paramOfHOL (ds.map declToHOL)
    rw [map_declOfHOL_declToHOL ds hdecls] at h
    have h' := congrArg (List.map Prod.fst) h
    rw [← h', List.map_map, List.map_map]
    rfl
  rw [← hnames]
  exact zip_map_fst toStringOfBytes _ (BitVec.ofNat width)

/-- Lookup-level bridge for the exact `make_funcs` map: the production
    `functionInfosHOL` finite map, decoded to exact carriers, is the exact
    `makeFuncsExactHOL` map of the encoded declarations. -/
theorem makeFuncsExactHOL_lookup_declToHOL {width : Nat} [NeZero width]
    (ds : List (Decl (BitVec width)))
    (hdecls : ∀ d ∈ ds, DeclByteRanged d) (key : MlS) :
    (makeFuncsExactHOL (functionsHOL (ds.map declToHOL))).lookup key =
      (functionInfosHOL ds (toStringOfBytes key)).map encodeFuncValue := by
  have hgen := flookup_alistToFmap_map_decode
    (f := Flapjack.Basis.Pure.MlString.toStringOfBytes)
    (h := decodeFuncValue) (decode := encodeFuncValue)
    (entries := makeFuncsEntriesHOL (functionsHOL (ds.map declToHOL))) key
    (fun e _ hab => Flapjack.toStringOfBytes_injective hab)
    (fun e _ => encodeFuncValue_decodeFuncValue e.2)
  rw [← prodFuncEntries_eq_map ds hdecls] at hgen
  have hexact : (makeFuncsExactHOL (functionsHOL (ds.map declToHOL))).lookup key =
      FLOOKUP (alistToFmap (makeFuncsEntriesHOL (functionsHOL (ds.map declToHOL)))) key := rfl
  have hprod : functionInfosHOL ds (toStringOfBytes key) =
      FLOOKUP (alistToFmap (prodFuncEntries ds)) (toStringOfBytes key) := by
    rw [functionInfosHOL_eq_makeFuncsHOL, makeFuncsHOL]
    change FUPDATE_LIST FEMPTY (prodFuncEntries ds).reverse (toStringOfBytes key) =
      FLOOKUP (alistToFmap (prodFuncEntries ds)) (toStringOfBytes key)
    rw [← alistToFmap_eq_fupdate_list_reverse]
    rfl
  rw [hexact, hprod]
  exact hgen.symm

/-- Lookup-level bridge for the exact `get_eids_from_decls` map. -/
theorem getEidsFromDeclsHOL_lookup_declToHOL {width : Nat} [NeZero width]
    (ds : List (Decl (BitVec width)))
    (hdecls : ∀ d ∈ ds, DeclByteRanged d) (key : MlS) :
    (getEidsFromDeclsHOL (ds.map declToHOL)).lookup key =
      panToCrepGetEidsFromDeclsHOL ds (toStringOfBytes key) := by
  have hgen := flookup_alistToFmap_map_decode
    (f := Flapjack.Basis.Pure.MlString.toStringOfBytes)
    (h := id) (decode := id) (entries := getEidsEntriesHOL (ds.map declToHOL)) key
    (fun e _ hab => Flapjack.toStringOfBytes_injective hab)
    (fun e _ => rfl)
  simp only [id_eq] at hgen
  rw [← prodEidsEntries_eq_map ds hdecls] at hgen
  have hexact : (getEidsFromDeclsHOL (ds.map declToHOL)).lookup key =
      FLOOKUP (alistToFmap (getEidsEntriesHOL (ds.map declToHOL))) key := rfl
  have hprod : panToCrepGetEidsFromDeclsHOL ds (toStringOfBytes key) =
      FLOOKUP (alistToFmap (prodEidsEntries ds)) (toStringOfBytes key) := by
    change FUPDATE_LIST FEMPTY (prodEidsEntries ds).reverse (toStringOfBytes key) =
      FLOOKUP (alistToFmap (prodEidsEntries ds)) (toStringOfBytes key)
    rw [← alistToFmap_eq_fupdate_list_reverse]
    rfl
  rw [hexact, hprod]
  simpa using hgen.symm

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

theorem compileParamVars_entries_nameRanged_bridge
    (params : List (VarName × Shape)) (offset : Nat)
    (hparams : ∀ p ∈ params, Flapjack.Pancake.PanLang.NameRanged p.1) :
    ∀ entry ∈ (compileParamVars params offset).1,
      Flapjack.Pancake.PanLang.NameRanged entry.1 := by
  induction params generalizing offset with
  | nil => simp [compileParamVars]
  | cons parameter params ih =>
      obtain ⟨name, shape⟩ := parameter
      have hname := hparams (name, shape) (by simp)
      have htail : ∀ p ∈ params, Flapjack.Pancake.PanLang.NameRanged p.1 := by
        intro p hp
        exact hparams p (by simp [hp])
      simp only [compileParamVars]
      intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with hhead | htailMem
      · cases hhead
        exact hname
      · exact ih (offset + Shape.shapeSize shape) htail entry htailMem

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
    compileParamVars_entries_nameRanged_bridge params 0 (fun p hp => (hparams p hp).1)
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

/-- The assembled byte-ranged bridge: transporting the production
    declaration-only compiler's output through the reviewed codecs equals the
    tagged exact `compile_to_crep` on the encoded declarations.

    Flapjack-specific infrastructure (no HOL original): HOL has no production
    `String`-keyed compiler counterpart, so this relation between the production
    `compileToCrepHOL` and the tagged exact `compileToCrepExactHOLW` is not a
    port of a HOL declaration and carries no `@[hol]` tag. It is stated on the
    `DeclByteRanged` side condition, which is exactly the hypothesis under which
    `declOfHOL_declToHOL` recovers production declarations. -/
theorem compileToCrepHOL_map_declToHOL {width : Nat} [NeZero width]
    (ds : List (Decl (BitVec width)))
    (hdecls : ∀ d ∈ ds, DeclByteRanged d) :
    (compileToCrepHOL ds).map
        (fun t => (ofString t.1, t.2.1, crepProgToHOL t.2.2)) =
      compileToCrepExactHOLW (ds.map declToHOL) := by
  have hthird : ∀ e ∈ functionEntries ds,
      crepProgToHOL
          (compFuncHOL (functionInfosHOL ds) (panToCrepGetEidsFromDeclsHOL ds)
            e.2.1 e.2.2.1) =
        compFuncExactHOLW
          (makeFuncsExactHOL (functionsHOL (ds.map declToHOL)))
          (getEidsFromDeclsHOL (ds.map declToHOL))
          (e.2.1.map paramToHOL) (progToHOL e.2.2.1) := by
    intro e he
    have hbridge := compileFunctionExactProductionBridge ds e hdecls he
    obtain ⟨_, hparams, _, _⟩ := functionEntries_byteRanged ds hdecls e he
    rw [← hbridge, crepProgToHOL_crepProgOfHOL]
    have hctx :
        panToCrepContextExactOfProduction
            (panToCrepMkCtxtHOL (panToCrepMakeVmapHOL e.2.1)
              (functionInfosHOL ds)
              (Shape.shapeSize (.comb (e.2.1.map Prod.snd)) - 1)
              (panToCrepGetEidsFromDeclsHOL ds))
            (panToCrepFunctionContextProductionEvidence ds e hdecls he) =
          mkCtxtExactHOL (panToCrepMakeVmapHOLExact (e.2.1.map paramToHOL))
            (makeFuncsExactHOL (functionsHOL (ds.map declToHOL)))
            (sizeOfShapeHOL (.comb ((e.2.1.map paramToHOL).map Prod.snd)) - 1)
            (getEidsFromDeclsHOL (ds.map declToHOL)) := by
      apply panToCrepContextExact_ext
      · apply holFiniteMapExact_ext
        intro key
        rw [panToCrepContextExactOfProduction_vars_lookup]
        exact (panToCrepMakeVmapHOLExactOfProductionParams_bridge e.2.1 hparams key).symm
      · apply holFiniteMapExact_ext
        intro key
        change (functionInfosHOL ds (toStringOfBytes key)).map
            (fun value => (value.1.map (fun p => (ofString p.1, shapeToHOL p.2)),
              shapeToHOL value.2)) =
          (makeFuncsExactHOL (functionsHOL (ds.map declToHOL))).lookup key
        rw [makeFuncsExactHOL_lookup_declToHOL ds hdecls key]
        rfl
      · apply holFiniteMapExact_ext
        intro key
        rw [panToCrepContextExactOfProduction_eids_lookup]
        exact (getEidsFromDeclsHOL_lookup_declToHOL ds hdecls key).symm
      · show Shape.shapeSize (.comb (e.2.1.map Prod.snd)) - 1 =
          sizeOfShapeHOL (.comb ((e.2.1.map paramToHOL).map Prod.snd)) - 1
        rw [show (e.2.1.map paramToHOL).map Prod.snd =
            (e.2.1.map Prod.snd).map shapeToHOL by
          simp only [List.map_map]
          apply List.map_congr_left
          intro p _
          rfl]
        simp only [sizeOfShapeHOL_comb, sizeOfShapesHOL_shapeToHOL, Shape.shapeSize]
    rw [hctx]
    rw [compFuncExactHOLW]
  have hlhs : (compileToCrepHOL ds).map
        (fun t => (ofString t.1, t.2.1, crepProgToHOL t.2.2)) =
      (functionEntries ds).map (fun e =>
        (ofString e.1, panToCrepVars e.2.1,
          crepProgToHOL (compFuncHOL (functionInfosHOL ds)
            (panToCrepGetEidsFromDeclsHOL ds) e.2.1 e.2.2.1))) := by
    simp only [compileToCrepHOL, List.map_map, ← functionInfosHOL_eq_makeFuncsHOL]
    rfl
  have hrhs : compileToCrepExactHOLW (ds.map declToHOL) =
      (functionEntries ds).map (fun e =>
        (ofString e.1, crepVarsHOL (e.2.1.map paramToHOL),
          compFuncExactHOLW (makeFuncsExactHOL (functionsHOL (ds.map declToHOL)))
            (getEidsFromDeclsHOL (ds.map declToHOL))
            (e.2.1.map paramToHOL) (progToHOL e.2.2.1))) := by
    simp only [compileToCrepExactHOLW, functionsHOL_map_declToHOL, List.map_map]
    apply List.map_congr_left
    intro e _
    simp [funEntryToHOL]
  rw [hlhs, hrhs]
  apply List.map_congr_left
  intro e he
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · rw [crepVarsHOL_map_paramToHOL]
  · exact hthird e he

end Flapjack
