import Flapjack.Pancake.CrepInline.Canonical

/-!
# Executed inline route vs. the exact tagged inline pass (first routing step)

The executable `flapjack-compile` inliner runs the production
`compileInlTopHOL` (`CrepInline/Pass.lean:1283`), while the exact HOL-shaped
tagged pass is `compileInlTopHOLExact` (`CrepInline/Canonical.lean:712`).  This
module starts proving that the two agree, so the executable route can be routed
through the reviewed exact definition.

This slice covers the empty-inline-name base case: with no inline candidate
names both inliners are the identity, so the production result and the exact
result agree under any decode/encode that the caller applies.  The relation is
Flapjack-specific infrastructure (there is no HOL declaration of it), so none of
these declarations carries a `@[hol]` tag.
-/

namespace Flapjack
open Flapjack.CrepInlineCanonical

namespace CrepInlineRoute

/-- With an empty inline-entry list the recursive inliner makes no change,
whatever the active name set is. -/
theorem crepInlineProgRecursive_nil [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1] (active : Std.HashSet FunName)
    (body : CrepProg α) :
    crepInlineProgRecursive ([] : List (CrepInlineEntry α)) active body = body := by
  fun_induction crepInlineProgRecursive ([] : List (CrepInlineEntry α)) active body <;>
    simp_all [crepInlineLookup]

/-- Production `compileInlTopHOL` is the identity on an empty inline-name list. -/
theorem compileInlTopHOL_nil [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    [OfNat α 0] [OfNat α 1] (functions : List (FunName × List Nat × CrepProg α)) :
    compileInlTopHOL ([] : List FunName) functions = functions := by
  simp only [compileInlTopHOL]
  have hfilter : functions.filter (fun function => ([] : List FunName).contains function.1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a _ hmem
    simp at hmem
  rw [hfilter]
  simp only [List.map_nil]
  have hmap : List.map (fun x : FunName × List Nat × CrepProg α =>
      (x.fst, x.2.fst, crepInlineProgRecursive []
        ((crepInlineActiveNames ([] : List (CrepInlineEntry α))).erase x.fst) x.2.snd))
      functions = List.map id functions := by
    apply List.map_congr_left
    intro a _
    simp only [id_eq]
    rw [crepInlineProgRecursive_nil]
  rw [hmap, List.map_id]

/-- Production `compileInlTopHOL` is the identity whenever no function in the
program is marked inlineable, i.e. the inlineable filter is empty.  This
generalizes `compileInlTopHOL_nil` from an empty inline-name list to a program
that simply contains none of the named functions. -/
theorem compileInlTopHOL_id_of_filter_nil [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1] (inlineNames : List FunName)
    (functions : List (FunName × List Nat × CrepProg α))
    (hfilter : functions.filter (fun function => inlineNames.contains function.1) = []) :
    compileInlTopHOL inlineNames functions = functions := by
  simp only [compileInlTopHOL]
  rw [hfilter]
  simp only [List.map_nil]
  have hmap : List.map (fun x : FunName × List Nat × CrepProg α =>
      (x.fst, x.2.fst, crepInlineProgRecursive []
        ((crepInlineActiveNames ([] : List (CrepInlineEntry α))).erase x.fst) x.2.snd))
      functions = List.map id functions := by
    apply List.map_congr_left
    intro a _
    simp only [id_eq]
    rw [crepInlineProgRecursive_nil]
  rw [hmap, List.map_id]

/-- On an everywhere-`none` inline map the exact recursive inliner makes no
change. -/
theorem inlineProgHOLCoreExact_lookup_none {width : Nat} [NeZero width]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (h : ∀ k, inlineable.lookup k = none)
    (program : CrepProgHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec program = program := by
  refine @inlineProgHOLCoreExact.induct width _ _ _
    (fun inlineable supportKeys support_spec prog =>
      ∀ (supportKeys₂ : List CrepInlineMapHOLName)
        (support₂ : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys₂),
        (∀ k, inlineable.lookup k = none) →
        inlineProgHOLCoreExact inlineable supportKeys₂ support₂ prog = prog)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    inlineable supportKeys support_spec program supportKeys support_spec h
  · intro inlineable supportKeys support_spec name arguments hl supportKeys₂ support₂ h
    simp only [inlineProgHOLCoreExact]
    rw [hl]
  · intro inlineable supportKeys support_spec name arguments argumentNames body hl ih
      supportKeys₂ support₂ h
    exact absurd (hl.symm.trans (h name)) (by simp)
  · intro inlineable supportKeys support_spec returnNames name arguments hd supportKeys₂ support₂ h
    simp only [inlineProgHOLCoreExact, hd, if_true]
  · intro inlineable supportKeys support_spec returnNames name arguments hd hl supportKeys₂ support₂ h
    simp only [inlineProgHOLCoreExact]
    simp only [if_neg hd]
    rw [hl]
  · intro inlineable supportKeys support_spec returnNames name arguments hd argumentNames body hl ih
      supportKeys₂ support₂ h
    exact absurd (hl.symm.trans (h name)) (by simp)
  · intro inlineable supportKeys support_spec returnNames handler body name arguments ih
      supportKeys₂ support₂ h
    simp only [inlineProgHOLCoreExact]
    rw [ih supportKeys₂ support₂ h]
  · intro inlineable supportKeys support_spec name value body ih supportKeys₂ support₂ h
    simp only [inlineProgHOLCoreExact]
    rw [ih supportKeys₂ support₂ h]
  · intro inlineable supportKeys support_spec first second ih1 ih2 supportKeys₂ support₂ h
    simp only [inlineProgHOLCoreExact]
    rw [ih1 supportKeys₂ support₂ h, ih2 supportKeys₂ support₂ h]
  · intro inlineable supportKeys support_spec condition first second ih1 ih2 supportKeys₂ support₂ h
    simp only [inlineProgHOLCoreExact]
    rw [ih1 supportKeys₂ support₂ h, ih2 supportKeys₂ support₂ h]
  · intro inlineable supportKeys support_spec condition body ih supportKeys₂ support₂ h
    simp only [inlineProgHOLCoreExact]
    rw [ih supportKeys₂ support₂ h]
  · intro inlineable supportKeys support_spec program hcn hcs hch hdec hseq hite hwhile
      supportKeys₂ support₂ h
    cases program with
    | call ret name args =>
        cases ret with
        | none => exact absurd rfl (hcn name args)
        | some p =>
            obtain ⟨rn, hb⟩ := p
            cases hb with
            | none => exact absurd rfl (hcs rn name args)
            | some hb' =>
                obtain ⟨handler, body⟩ := hb'
                exact absurd rfl (hch rn handler body name args)
    | dec name value body => exact absurd rfl (hdec name value body)
    | seq first second => exact absurd rfl (hseq first second)
    | ite c a b => exact absurd rfl (hite c a b)
    | «while» c b => exact absurd rfl (hwhile c b)
    | skip => simp only [inlineProgHOLCoreExact]
    | assign name value => simp only [inlineProgHOLCoreExact]
    | primitive names operator args => simp only [inlineProgHOLCoreExact]
    | store address value => simp only [inlineProgHOLCoreExact]
    | store32 address value => simp only [inlineProgHOLCoreExact]
    | storeByte address value => simp only [inlineProgHOLCoreExact]
    | storeGlob address value => simp only [inlineProgHOLCoreExact]
    | «break» label => simp only [inlineProgHOLCoreExact]
    | «continue» label => simp only [inlineProgHOLCoreExact]
    | extCall function configuration configurationLength array arrayLength =>
        simp only [inlineProgHOLCoreExact]
    | raise exception => simp only [inlineProgHOLCoreExact]
    | «return» values => simp only [inlineProgHOLCoreExact]
    | shMem operator name address => simp only [inlineProgHOLCoreExact]
    | tick => simp only [inlineProgHOLCoreExact]

/-- The support-certified exact inliner is the identity on an everywhere-`none`
inline map. -/
theorem compileInlProgHOLExactWithSupport_eq_self {width : Nat} [NeZero width]
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inl_fs.lookup key ≠ none → key ∈ supportKeys)
    (h : ∀ k, inl_fs.lookup k = none)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    compileInlProgHOLExactWithSupport inl_fs supportKeys support_spec prog = prog := by
  unfold compileInlProgHOLExactWithSupport
  have hmap : List.map (fun triple : CrepInlineMapHOLName × List Nat × CrepProgHOL width =>
      (triple.fst, triple.snd.fst,
        inlineProgHOLCoreExact (inl_fs.erase triple.fst)
          (List.filter (fun key => key != triple.fst) supportKeys)
          (HolFiniteMapExact.erase_support inl_fs supportKeys support_spec triple.fst)
          triple.snd.snd)) prog = List.map id prog := by
    apply List.map_congr_left
    intro triple _
    simp only [id_eq]
    have herase : ∀ k, (inl_fs.erase triple.fst).lookup k = none := by
      intro k
      rw [HolFiniteMapExact.lookup_erase]
      by_cases hk : triple.fst == k <;> simp [FDOMSUB, hk, h k]
    rw [inlineProgHOLCoreExact_lookup_none (inl_fs.erase triple.fst)
      (supportKeys.filter (fun k => k != triple.fst))
      (HolFiniteMapExact.erase_support inl_fs supportKeys support_spec triple.fst) herase triple.snd.snd]
  rw [hmap, List.map_id]

/-- The plain exact inliner is the identity on an everywhere-`none` inline map. -/
theorem compileInlProgHOLExact_eq_self {width : Nat} [NeZero width]
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (h : ∀ k, inl_fs.lookup k = none)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    compileInlProgHOLExact inl_fs prog = prog := by
  rw [← compileInlProgHOLExactWithSupport_eq_compileInlProgHOLExact inl_fs
    (Classical.choose inl_fs.finiteSupport)
    (Classical.choose_spec inl_fs.finiteSupport) prog]
  exact compileInlProgHOLExactWithSupport_eq_self inl_fs _ _ h prog

/-- Exact `compileInlTopHOLExact` is the identity on an empty inline-name list. -/
theorem compileInlTopHOLExact_nil {width : Nat} [NeZero width]
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    compileInlTopHOLExact ([] : List CrepInlineMapHOLName) prog = prog := by
  rw [compileInlTopHOLExact_eq_compileInlProgHOLExact]
  have hfilter : prog.filter (fun triple => ([] : List CrepInlineMapHOLName).contains triple.1) =
      [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a _ hmem
    simp at hmem
  rw [hfilter]
  exact compileInlProgHOLExact_eq_self (alistToFmapHOLExact [])
    (by
      intro k
      simp only [alistToFmapHOLExact, List.reverse_nil, HolFiniteMapExact.lookup_updateList,
        FUPDATE_LIST_nil, HolFiniteMapExact.lookup_empty]) prog

/-- First routing step, decoded form: on an empty inline-name list the exact
tagged pass maps the decoded production program to the decode of the production
result.  The decode is arbitrary, so this is the empty-name base case of the
executed-route/exact-route relation. -/
theorem compileInlTopHOLExact_nil_map [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1] {width : Nat} [NeZero width]
    (decode : FunName × List Nat × CrepProg α →
      CrepInlineMapHOLName × List Nat × CrepProgHOL width)
    (functions : List (FunName × List Nat × CrepProg α)) :
    compileInlTopHOLExact ([] : List CrepInlineMapHOLName) (functions.map decode) =
      (compileInlTopHOL ([] : List FunName) functions).map decode := by
  rw [compileInlTopHOL_nil, compileInlTopHOLExact_nil]

/-- Association-list agreement, generic half: `FUPDATE_LIST` distributes over
list append (`FUPDATE_LIST` is `List.foldl FUPDATE`). -/
theorem fupdateList_append {α β : Type} [BEq α] (f : FiniteMap α β)
    (xs ys : List (α × β)) :
    FUPDATE_LIST f (xs ++ ys) = FUPDATE_LIST (FUPDATE_LIST f xs) ys := by
  induction xs generalizing f with
  | nil => simp [FUPDATE_LIST]
  | cons x xs ih => simp only [List.cons_append, FUPDATE_LIST_cons]; exact ih (FUPDATE f x)

/-- `BEq` is symmetric under `LawfulBEq`. -/
theorem beq_comm {α : Type} [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst h; rfl
  · have h1 : (a == b) = false := beq_eq_false_iff_ne.mpr h
    have h2 : (b == a) = false := beq_eq_false_iff_ne.mpr (fun he => h he.symm)
    rw [h1, h2]

/-- Association-list agreement: the production inline-candidate index
`crepInlineLookup` (first occurrence wins, `Pass.lean:22`) is the `FLOOKUP` of
the `FUPDATE_LIST` map over the reversed entry list.  This is exactly the map
read by the exact `alistToFmapHOLExact` (`Canonical.lean:612`, whose lookup is
`FUPDATE_LIST FEMPTY entries.reverse`), so it is the carrier half of the
executed-vs-exact candidate-index relation; the remaining half is the
`toStringOfBytes` name codec. -/
theorem crepInlineLookup_eq_fupdateList {α : Type} [BEq FunName] [LawfulBEq FunName]
    (name : FunName) (entries : List (CrepInlineEntry α)) :
    crepInlineLookup name entries =
      FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap FunName (List Nat × CrepProg α))
        entries.reverse) name := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [crepInlineLookup, List.reverse_cons, fupdateList_append]
      rw [FUPDATE_LIST_cons, FUPDATE_LIST_nil, FLOOKUP_update]
      rw [beq_comm name entry.1, ih]

open Flapjack.Basis.Pure.MlString in
/-- `toStringOfBytes` is injective on `MlString` (its right inverse is
    `ofString`, `ofString_toStringOfBytes`).  This is the forward half of the
    executed-vs-exact name codec: equal `String` encodings identify the
    `MlString` inline-map keys. -/
theorem toStringOfBytes_injective {m1 m2 : MlString}
    (h : toStringOfBytes m1 = toStringOfBytes m2) : m1 = m2 := by
  have hc := congrArg ofString h
  rwa [ofString_toStringOfBytes, ofString_toStringOfBytes] at hc

open Flapjack.Basis.Pure.MlString in
/-- An `MlString` equals `ofString s` exactly when their byte encodings agree. -/
theorem ofString_eq_iff_toStringOfBytes_eq {s : String} {m : MlString} :
    ofString s = m ↔ toStringOfBytes (ofString s) = toStringOfBytes m := by
  constructor
  · intro h; rw [h]
  · intro h
    have hc := congrArg ofString h
    simpa only [ofString_toStringOfBytes] using hc

open Flapjack.Basis.Pure.MlString in
/-- `BEq` agreement under the name codec: for a byte-ranged `String` the
    `ofString` insertion commutes with `==` and `toStringOfBytes`.  This is the
    comparison half of the executed-vs-exact name codec. -/
theorem beq_ofString_eq {s : String} {m : MlString} (hs : CrepNameRanged s) :
    (ofString s == m) = (s == toStringOfBytes m) := by
  have hiff : ofString s = m ↔ s = toStringOfBytes m := by
    rw [ofString_eq_iff_toStringOfBytes_eq, toStringOfBytes_ofString_of_bytes s hs]
  by_cases h : ofString s = m
  · rw [beq_iff_eq.mpr h, beq_iff_eq.mpr (hiff.mp h)]
  · have hm : s ≠ toStringOfBytes m := fun hs' => h (hiff.mpr hs')
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hm]

open Flapjack.Basis.Pure.MlString in
/-- Membership under the name codec: for a byte-ranged `String`, membership in
    the `toStringOfBytes`-image of an `MlString` list is membership of its
    `ofString` lift.  This is the filter-predicate half of the
    executed-vs-exact inline-candidate agreement. -/
theorem contains_map_toStringOfBytes {ms : List MlString} (s : String)
    (hs : CrepNameRanged s) :
    (ms.map toStringOfBytes).contains s = ms.contains (ofString s) := by
  induction ms with
  | nil => simp only [List.map_nil, List.contains_nil]
  | cons m ms ih =>
      simp only [List.map_cons, List.contains_cons]
      rw [beq_ofString_eq hs, ih]

open Flapjack.Basis.Pure.MlString in
/-- Boolean form of `contains_map_toStringOfBytes`. -/
theorem map_eq_iff_contains {ms : List MlString} (s : String) (hs : CrepNameRanged s) :
    (ms.map toStringOfBytes).contains s = true ↔ ms.contains (ofString s) = true := by
  rw [contains_map_toStringOfBytes s hs]

open Flapjack.Basis.Pure.MlString in
/-- Name-membership agreement under the `toStringOfBytes` codec on byte-ranged names:
    given `inlineNames` is the `toStringOfBytes` image of `inl_fname`, filtering by the
    production String name is the image of filtering by the exact `MlString` name. -/
theorem contains_toStringOfBytes_agree {inlineNames : List FunName}
    {inl_fname : List CrepInlineMapHOLName}
    (hinl : inlineNames = inl_fname.map toStringOfBytes) {s : String}
    (hs : CrepNameRanged s) :
    inlineNames.contains s = inl_fname.contains (ofString s) := by
  rw [hinl, contains_map_toStringOfBytes s hs]

open Flapjack.Basis.Pure.MlString in
/-- Filter/name agreement across the codec: if the production function-name list is the
    `toStringOfBytes` image of the exact `MlString` list and every production name is
    byte-ranged, the production filter on `inlineNames` maps to the exact filter on
    `inl_fname`. -/
theorem filter_names_toStringOfBytes {l1 : List FunName} {l2 : List CrepInlineMapHOLName}
    {inlineNames : List FunName} {inl_fname : List CrepInlineMapHOLName}
    (h : l1 = l2.map toStringOfBytes)
    (hinl : inlineNames = inl_fname.map toStringOfBytes)
    (hrange : ∀ s ∈ l1, CrepNameRanged s) :
    l1.filter (fun s => inlineNames.contains s) =
      (l2.filter (fun m => inl_fname.contains m)).map toStringOfBytes := by
  subst h
  revert hrange
  induction l2 with
  | nil => intro hrange; simp
  | cons m rest ih =>
      intro hrange
      have hm : toStringOfBytes m ∈ (m :: rest).map toStringOfBytes := by
        simp
      have hsub : ∀ s ∈ rest.map toStringOfBytes, CrepNameRanged s :=
        fun s hs => hrange s (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hs)
      have hcond : inlineNames.contains (toStringOfBytes m) = inl_fname.contains m := by
        rw [contains_toStringOfBytes_agree hinl (hrange (toStringOfBytes m) hm),
          ofString_toStringOfBytes]
      simp only [List.map_cons, List.filter_cons]
      rw [hcond]
      by_cases hc : inl_fname.contains m
      · simp only [hc, if_true]
        exact congrArg (toStringOfBytes m :: ·) (ih hsub)
      · simp only [hc]
        exact ih hsub

open Flapjack.Basis.Pure.MlString

/-- Name codec symmetry: for a byte-ranged `String` name, comparing the
`MlString` image under `toStringOfBytes` against `s` agrees with comparing
the `String` against `toStringOfBytes`. Untagged Flapjack-specific support. -/
theorem beq_toStringOfBytes_eq_ofString {s : String} (hs : CrepNameRanged s)
    (m : MlString) : (toStringOfBytes m == s) = (m == ofString s) := by
  rw [beq_comm (toStringOfBytes m) s, ← beq_ofString_eq hs, beq_comm (ofString s) m]

/-- Codec-lifted alist lookup: a `FUPDATE_LIST` over codec-translated entries
mirrors the exact lookup under `ofString`/`Option.map decode`. -/
theorem flookup_fupdateList_codec {β γ : Type} [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (base1 : FiniteMap String γ) (base2 : FiniteMap CrepInlineMapHOLName β)
    (decode : β → γ)
    (hbase : ∀ t, CrepNameRanged t → base1 t = (base2 (ofString t)).map decode)
    (entries : List (CrepInlineMapHOLName × β)) (s : String) (hs : CrepNameRanged s) :
    FLOOKUP (FUPDATE_LIST base1
        (entries.map (fun e => (toStringOfBytes e.1, decode e.2)))) s =
      (FLOOKUP (FUPDATE_LIST base2 entries) (ofString s)).map decode := by
  induction entries generalizing base1 base2 with
  | nil =>
      simp only [List.map_nil, FUPDATE_LIST_nil, FLOOKUP]
      exact hbase s hs
  | cons entry rest ih =>
      rw [List.map_cons, FUPDATE_LIST_cons, FUPDATE_LIST_cons]
      apply ih
      intro t ht
      change FLOOKUP (FUPDATE base1 (toStringOfBytes entry.fst, decode entry.snd)) t =
        Option.map decode (FLOOKUP (FUPDATE base2 entry) (ofString t))
      rw [FLOOKUP_update, FLOOKUP_update, beq_toStringOfBytes_eq_ofString ht entry.1]
      by_cases hc : (entry.1 == ofString t) = true
      · split <;> simp_all
      · split
        · simp_all
        · exact hbase t ht

/-- `alistToFmapHOLExact` looked up through the codec equals the production
`FUPDATE_LIST` over the translated entries. Untagged support. -/
theorem alistToFmapHOLExact_codec_lookup {width : Nat} [NeZero width] {γ : Type}
    [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (decode : (List Nat × CrepProgHOL width) → γ)
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width)))
    (s : String) (hs : CrepNameRanged s) :
    FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap String γ)
        ((entries.map (fun e => (toStringOfBytes e.1, decode e.2))).reverse)) s =
      ((alistToFmapHOLExact entries).lookup (ofString s)).map decode := by
  rw [lookup_alistToFmapHOLExact]
  rw [← List.map_reverse]
  exact flookup_fupdateList_codec FEMPTY FEMPTY decode
    (fun t _ => by simp only [FEMPTY, Option.map_none]) entries.reverse s hs

/-- The production inline-candidate lookup `crepInlineLookup` over the codec
translated entry list equals the exact `alistToFmapHOLExact` lookup under the
name codec. Untagged; the remaining piece is the body/recursion agreement. -/
theorem crepInlineLookup_codec {width : Nat} [NeZero width] {α : Type}
    (bodyDecode : CrepProgHOL width → CrepProg α)
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width)))
    (s : String) (hs : CrepNameRanged s) :
    crepInlineLookup s (entries.map (fun e =>
        (toStringOfBytes e.1, (e.2.1, bodyDecode e.2.2)))) =
      ((alistToFmapHOLExact entries).lookup (ofString s)).map
        (fun e => (e.1, bodyDecode e.2)) := by
  rw [crepInlineLookup_eq_fupdateList]
  exact alistToFmapHOLExact_codec_lookup (fun e => (e.1, bodyDecode e.2)) entries s hs

/-- `crepExpToHOL` sends `CrepExp.var` to `CrepExpHOL.var`. -/
theorem crepExpToHOL_var_map {width : Nat} [NeZero width] (names : List Nat) :
    (names.map (CrepExp.var (α := BitVec width))).map crepExpToHOL =
      names.map CrepExpHOL.var := by
  induction names with
  | nil => rfl
  | cons n ns ih => simp only [List.map_cons, ih, crepExpToHOL]

/-- Executed argument loading lifts to the exact argument loading under the
    `crepProgToHOL` codec. -/
theorem crepProgToHOL_crepArgLoad {width : Nat} [NeZero width]
    (temporaryNames argumentNames : List Nat)
    (arguments : List (CrepExp (BitVec width))) (body : CrepProg (BitVec width)) :
    crepProgToHOL (crepArgLoad temporaryNames arguments argumentNames body) =
      argLoadHOLExact temporaryNames (arguments.map crepExpToHOL) argumentNames
        (crepProgToHOL body) := by
  simp only [crepArgLoad, argLoadHOLExact, crepProgToHOL_nestedDecs]
  rw [crepExpToHOL_var_map]

/-- Executed inline-tail lifting: `crepInlineTail` agrees with the exact
    `inlineTailHOLExact` under the `crepProgToHOL` codec. -/
theorem crepProgToHOL_crepInlineTail {width : Nat} [NeZero width]
    (program : CrepProg (BitVec width)) :
    crepProgToHOL (crepInlineTail program) = inlineTailHOLExact (crepProgToHOL program) := by
  simp [crepInlineTail, inlineTailHOLExact, crepProgToHOL]

/-- The call shapes that `crepTransformEoc` leaves unchanged are matched by the
    exact `transformEocHOLExact`, so the identity case of the well-founded
    induction is vacuous for every call return shape. -/
private theorem crepCallDefault {width : Nat} [NeZero width] (returnNames : List Nat)
    (name : FunName) (args : List (CrepExp (BitVec width)))
    (ret : Option (List Nat × Option (BitVec width × CrepProg (BitVec width))))
    (h1 : ret ≠ none) (h2 : ∀ names, ret ≠ some (names, none))
    (h3 : ∀ names handler body, ret ≠ some (names, some (handler, body))) :
    crepProgToHOL (CrepProg.call ret name args) =
      transformEocHOLExact returnNames (crepProgToHOL (CrepProg.call ret name args)) := by
  rcases ret with _ | ⟨names, r⟩
  · exact absurd rfl h1
  · rcases r with _ | ⟨handler, body⟩
    · exact absurd rfl (h2 names)
    · exact absurd rfl (h3 names handler body)

/-- Executed `crepTransformEoc` lifts to the exact `transformEocHOLExact` under
    the `crepProgToHOL` codec. -/
theorem crepProgToHOL_crepTransformEoc {width : Nat} [NeZero width]
    (returnNames : List Nat) (program : CrepProg (BitVec width)) :
    crepProgToHOL (crepTransformEoc returnNames program) =
      transformEocHOLExact returnNames (crepProgToHOL program) := by
  fun_induction crepTransformEoc returnNames program with
  | case1 values =>
      simp only [transformEocHOLExact, crepProgToHOL, crepProgToHOL_crepNestedSeqHOL]
      rw [List.map_zipWith, List.zipWith_map_right]
      simp only [crepProgToHOL]
  | case2 name arguments => simp only [transformEocHOLExact, crepProgToHOL]
  | case3 names name arguments => simp only [transformEocHOLExact, crepProgToHOL]
  | case4 names handler body name arguments ih =>
      simp only [transformEocHOLExact, crepProgToHOL, ih]
  | case5 name value body ih => simp only [transformEocHOLExact, crepProgToHOL, ih]
  | case6 condition body ih => simp only [transformEocHOLExact, crepProgToHOL, ih]
  | case7 first second ih1 ih2 => simp only [transformEocHOLExact, crepProgToHOL, ih1, ih2]
  | case8 condition thenBranch elseBranch ih1 ih2 =>
      simp only [transformEocHOLExact, crepProgToHOL, ih1, ih2]
  | case9 program =>
      cases program with
      | call ret nm ar =>
          rename_i hr hc hcn hcs hdec hwhile hseq hite
          rcases ret with _ | ⟨names, r⟩
          · exact absurd rfl (hc nm ar)
          · rcases r with _ | ⟨handler, body⟩
            · exact absurd rfl (hcn names nm ar)
            · exact absurd rfl (hcs names handler body nm ar)
      | _ => simp_all [transformEocHOLExact, crepProgToHOL]

end CrepInlineRoute
end Flapjack
