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

/-- Executed `crepTransformBranch` lifts to the exact `transformBranchHOLExact`
    under the `crepProgToHOL` codec. -/
theorem crepProgToHOL_crepTransformBranch {width : Nat} [NeZero width] (loopDepth : Nat)
    (returnNames : List Nat) (program : CrepProg (BitVec width)) :
    crepProgToHOL (crepTransformBranch loopDepth returnNames program) =
      transformBranchHOLExact loopDepth returnNames (crepProgToHOL program) := by
  fun_induction crepTransformBranch loopDepth returnNames program with
  | case1 =>
      simp_all only [transformBranchHOLExact, crepProgToHOL,
        crepProgToHOL_crepNestedSeqHOL, List.map_zipWith, List.zipWith_map_right]
  | case2 => simp_all only [transformBranchHOLExact, crepProgToHOL]
  | case3 => simp_all only [transformBranchHOLExact, crepProgToHOL]
  | case4 => simp_all only [transformBranchHOLExact, crepProgToHOL]
  | case5 => simp_all only [transformBranchHOLExact, crepProgToHOL]
  | case6 => simp_all only [transformBranchHOLExact, crepProgToHOL]
  | case7 => simp_all only [transformBranchHOLExact, crepProgToHOL]
  | case8 => simp_all only [transformBranchHOLExact, crepProgToHOL]
  | case9 lp program =>
      cases program with
      | call ret nm ar =>
          rename_i hr hc hcn hcs hdec hwhile hseq hite
          rcases ret with _ | ⟨names, r⟩
          · exact absurd rfl (hc nm ar)
          · rcases r with _ | ⟨handler, body⟩
            · exact absurd rfl (hcn names nm ar)
            · exact absurd rfl (hcs names handler body nm ar)
      | _ => simp_all [transformBranchHOLExact, crepProgToHOL]

/-- `nestedDecs` over a constant-zero value list maps to `List.replicate` of the
    exact constant under the codec. -/
private theorem crepExpMap_const_replicate {width : Nat} [NeZero width] (l : List Nat) :
    (l.map (fun _ => CrepExp.const (0 : BitVec width))).map crepExpToHOL =
      List.replicate l.length (CrepExpHOL.const 0) := by
  induction l with
  | nil => rfl
  | cons n t ih =>
      have h : crepExpToHOL (CrepExp.const (0 : BitVec width)) = CrepExpHOL.const 0 := by
        simp [crepExpToHOL]
      simp only [List.map_cons]
      rw [ih, h]
      rfl

/-- Executed `crepInlineNontail` lifts to the exact `inlineNontailHOLExact`
    under the `crepProgToHOL` codec. -/
theorem crepProgToHOL_crepInlineNontail {width : Nat} [NeZero width]
    (program : CrepProg (BitVec width))
    (returnNames temporaryReturns temporaryNames : List Nat)
    (arguments : List (CrepExp (BitVec width))) (argumentNames : List Nat) :
    crepProgToHOL (crepInlineNontail program returnNames temporaryReturns temporaryNames
        arguments argumentNames) =
      inlineNontailHOLExact (crepProgToHOL program) returnNames temporaryReturns temporaryNames
        (arguments.map crepExpToHOL) argumentNames := by
  unfold crepInlineNontail inlineNontailHOLExact
  rw [crepProgToHOL_nestedDecs]
  congr 1
  · exact crepExpMap_const_replicate temporaryReturns
  · simp only [crepProgToHOL, crepProgToHOL_crepArgLoad, crepProgToHOL_crepNestedSeqHOL]
    rw [List.map_zipWith]
    have hfun : (fun x y => crepProgToHOL (CrepProg.assign (α := BitVec width) x
        (CrepExp.var (α := BitVec width) y))) =
        (fun name temporary => CrepProgHOL.assign name (CrepExpHOL.var temporary)) := by
      funext name temporary
      simp [crepProgToHOL, crepExpToHOL]
    rw [hfun]

def crepEarlyExitToHOL : CrepEarlyExit → CrepEarlyExitHOL
  | .exception => .exception
  | .return => .return
  | .loopExit => .loopExit

/-- `crepMergeExit` agrees with the exact `crepMergeExitHOL` under
    `crepEarlyExitToHOL`. -/
theorem crepMergeExit_map (a b : Option CrepEarlyExit) :
    (crepMergeExit a b).map crepEarlyExitToHOL =
      crepMergeExitHOL (a.map crepEarlyExitToHOL) (b.map crepEarlyExitToHOL) := by
  cases a with
  | none => cases b with
    | none => rfl
    | some eb => cases eb <;> rfl
  | some ea => cases ea with
    | «return» => cases b with
      | none => rfl
      | some eb => cases eb <;> rfl
    | «exception» => cases b with
      | none => rfl
      | some eb => cases eb <;> rfl
    | «loopExit» => cases b with
      | none => rfl
      | some eb => cases eb <;> rfl

/-- The executed unreachability pass `crepUnreachElim` (`CrepInline.lean:340`)
    agrees with the exact tagged `unreachElimHOLExact`
    (`CrepInline.lean:189`) under `crepProgToHOL`.  The stored early-exit is
    related by `crepEarlyExitToHOL`.  Untagged Flapjack-specific infrastructure
    (there is no HOL declaration of this cross-representation relation). -/
theorem crepProgToHOL_crepUnreachElim {width : Nat} [NeZero width] (program : CrepProg (BitVec width)) :
    (crepProgToHOL (crepUnreachElim program).1,
        (crepUnreachElim program).2.map crepEarlyExitToHOL) =
      unreachElimHOLExact (crepProgToHOL program) := by
  apply crepUnreachElim.induct (motive := fun program =>
    ∀ (q : CrepProg (BitVec width)) (r : Option CrepEarlyExit),
      crepUnreachElim program = (q, r) →
      (crepProgToHOL q, r.map crepEarlyExitToHOL) =
        unreachElimHOLExact (crepProgToHOL program))
  · intro values q r h
    rw [crepUnreachElim.eq_def] at h
    cases h
    simp [crepProgToHOL, unreachElimHOLExact, crepEarlyExitToHOL]
  · intro exception q r h
    rw [crepUnreachElim.eq_def] at h
    cases h
    simp [crepProgToHOL, unreachElimHOLExact, crepEarlyExitToHOL]
  · intro label q r h
    rw [crepUnreachElim.eq_def] at h
    cases h
    simp [crepProgToHOL, unreachElimHOLExact, crepEarlyExitToHOL]
  · intro label q r h
    rw [crepUnreachElim.eq_def] at h
    cases h
    simp [crepProgToHOL, unreachElimHOLExact, crepEarlyExitToHOL]
  · intro first second second' secondExit hfirst hsome ihFirst q r h
    have hunf : crepUnreachElim (.seq first second) = (second', secondExit) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hfirst]
      simp [hsome]
    rw [hunf] at h
    cases h
    simp only [crepProgToHOL, unreachElimHOLExact]
    rw [← ihFirst second' secondExit hfirst]
    simp only [Option.isSome_map, hsome, if_true]
  · intro first second second' secondExit hfirst hnotsome second'' secondExit' hsecond ihFirst ihSecond q r h
    have hunf : crepUnreachElim (.seq first second) = (.seq second' second'', secondExit') := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hfirst]
      simp [hnotsome, hsecond]
    rw [hunf] at h
    cases h
    simp only [crepProgToHOL, unreachElimHOLExact]
    rw [← ihFirst second' secondExit hfirst, ← ihSecond second'' secondExit' hsecond]
    simp only [Option.isSome_map, hnotsome, Bool.false_eq_true, if_false]
  · intro name value body body' bodyExit hbody ih q r h
    have hunf : crepUnreachElim (.dec name value body) = (.dec name value body', bodyExit) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hbody]
    rw [hunf] at h
    cases h
    simp only [crepProgToHOL, unreachElimHOLExact]
    rw [← ih body' bodyExit hbody]
  · intro condition thenBranch elseBranch then' thenExit hthen then'' elseExit helse ihThen ihElse q r h
    have hunf : crepUnreachElim (.ite condition thenBranch elseBranch) =
        (.ite condition then' then'', crepMergeExit thenExit elseExit) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hthen]
      dsimp only
      rw [helse]
    rw [hunf] at h
    cases h
    simp only [crepProgToHOL, unreachElimHOLExact]
    rw [← ihThen then' thenExit hthen, ← ihElse then'' elseExit helse,
      ← crepMergeExit_map thenExit elseExit]
  · intro condition body body' bodyExit hbody ih q r h
    have hunf : crepUnreachElim (.while condition body) = (.while condition body', none) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hbody]
    rw [hunf] at h
    cases h
    simp only [crepProgToHOL, unreachElimHOLExact]
    rw [← ih body' bodyExit hbody]
    simp only [Option.map_none]
  · intro name arguments q r h
    rw [crepUnreachElim.eq_def] at h
    cases h
    simp [crepProgToHOL, unreachElimHOLExact, crepEarlyExitToHOL]
  · intro names name arguments q r h
    rw [crepUnreachElim.eq_def] at h
    cases h
    simp [crepProgToHOL, unreachElimHOLExact]
  · intro names handler body name arguments second' secondExit hbody ih q r h
    have hunf : crepUnreachElim (.call (some (names, some (handler, body))) name arguments) =
        (.call (some (names, some (handler, second'))) name arguments, none) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hbody]
    rw [hunf] at h
    cases h
    simp only [crepProgToHOL, unreachElimHOLExact]
    rw [← ih second' secondExit hbody]
    simp only [Option.map_none]
  · intro program hret hraise hbreak hcontinue hseq hdec hite hwhile hcallnone hcallsomenone hcallsomesome q r h
    cases program with
    | skip =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | assign name value =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | primitive names operator args =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | store address value =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | store32 address value =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | storeByte address value =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | storeGlob address value =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | extCall function configuration configurationLength array arrayLength =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | shMem operator name address =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | tick =>
        rw [crepUnreachElim.eq_def] at h; cases h
        simp [crepProgToHOL, unreachElimHOLExact]
    | «return» values => exact absurd rfl (hret values)
    | «raise» exception => exact absurd rfl (hraise exception)
    | «break» label => exact absurd rfl (hbreak label)
    | «continue» label => exact absurd rfl (hcontinue label)
    | «seq» first second => exact absurd rfl (hseq first second)
    | «dec» name value body => exact absurd rfl (hdec name value body)
    | «ite» condition thenBranch elseBranch => exact absurd rfl (hite condition thenBranch elseBranch)
    | «while» condition body => exact absurd rfl (hwhile condition body)
    | «call» ret nm ar =>
        cases ret with
        | none => exact absurd rfl (hcallnone nm ar)
        | some pair =>
            obtain ⟨names, rest⟩ := pair
            cases rest with
            | none => exact absurd rfl (hcallsomenone names nm ar)
            | some hr =>
                obtain ⟨handler, body⟩ := hr
                exact absurd rfl (hcallsomesome names handler body nm ar)
  · obtain ⟨a, b⟩ := crepUnreachElim program
    rfl

private theorem crepInlineActiveNames_contains_any_go [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] {α : Type} (inlineable : List (CrepInlineEntry α))
    (name : FunName) (s : Std.HashSet FunName) :
    (inlineable.foldl (fun names entry => names.insert entry.1) s).contains name =
      (s.contains name || inlineable.any (fun entry => entry.1 == name)) := by
  induction inlineable generalizing s with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons, List.any_cons]
      rw [ih (s.insert entry.1), Std.HashSet.contains_insert]
      rw [Bool.or_comm (entry.1 == name) (s.contains name), Bool.or_assoc]

/-- Membership in the production active-name set (`crepInlineActiveNames`) is
    first-match lookup success in the inline-candidate list.  Untagged
    Flapjack-specific infrastructure. -/
theorem crepInlineActiveNames_contains_any [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] {α : Type} (inlineable : List (CrepInlineEntry α))
    (name : FunName) :
    (crepInlineActiveNames inlineable).contains name =
      inlineable.any (fun entry => entry.1 == name) := by
  unfold crepInlineActiveNames
  rw [crepInlineActiveNames_contains_any_go inlineable name ∅,
    Std.HashSet.contains_empty, Bool.false_or]

/-- First-match lookup success is the same `any` used for active-name
    membership.  Untagged Flapjack-specific infrastructure. -/
theorem crepInlineLookup_isSome_any [BEq FunName] [LawfulBEq FunName]
    {α : Type} (name : FunName) (inlineable : List (CrepInlineEntry α)) :
    (crepInlineLookup name inlineable).isSome =
      inlineable.any (fun entry => entry.1 == name) := by
  induction inlineable with
  | nil => rfl
  | cons entry rest ih =>
      simp only [crepInlineLookup, List.any_cons]
      by_cases h : (name == entry.1) = true
      · have h' : (entry.1 == name) = true := by rw [beq_comm entry.1 name]; exact h
        rw [if_pos h, h', Bool.true_or]
        rfl
      · have hnf : (name == entry.1) = false := by
          cases hv : (name == entry.1) <;> simp_all
        have h' : (entry.1 == name) = false := by rw [beq_comm entry.1 name]; exact hnf
        rw [if_neg h, ih, h', Bool.false_or]

/-- The executable active-name guard equals the exact finite-map lookup used by
    `inlineProgHOLCoreExact`.  Untagged Flapjack-specific infrastructure. -/
theorem crepInlineActiveNames_contains_eq [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] {α : Type} (inlineable : List (CrepInlineEntry α))
    (name : FunName) :
    (crepInlineActiveNames inlineable).contains name =
      (crepInlineLookup name inlineable).isSome := by
  rw [crepInlineActiveNames_contains_any inlineable name,
    ← crepInlineLookup_isSome_any name inlineable]

/-- The executed `crepExpVars` family over a list of production expressions
    agrees with the exact `crepExpVarsHOL` read through `crepExpToHOL`.
    Untagged Flapjack-specific infrastructure. -/
theorem crepExpVars_flatMap_codec {width : Nat} [NeZero width]
    (arguments : List (CrepExp (BitVec width))) :
    arguments.flatMap crepExpVars =
      (arguments.map crepExpToHOL).flatMap crepExpVarsHOL := by
  induction arguments with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]
      exact congrArg (fun x => x ++ (as.map crepExpToHOL).flatMap crepExpVarsHOL)
        (crepExpVarsW_eq_crepExpVarsHOL_crepExpToHOL (width := width) a)

/-- The executed temporary-name generator `crepInlineTmpNames` equals the exact
    `genlistSuccAddHOLExact` at the folded maxima of the argument variables.
    Untagged Flapjack-specific infrastructure. -/
theorem crepInlineTmpNames_codec {width : Nat} [NeZero width]
    (arguments : List (CrepExp (BitVec width))) (argumentNames : List Nat) :
    crepInlineTmpNames (arguments.flatMap crepExpVars) argumentNames =
      genlistSuccAddHOLExact
        (max (((arguments.map crepExpToHOL).flatMap crepExpVarsHOL).foldl max 0)
          (argumentNames.foldl max 0))
        argumentNames.length := by
  unfold crepInlineTmpNames genlistSuccAddHOLExact
  rw [crepExpVars_flatMap_codec]

/-- The executed `crepInlineCallBody` at `none` return info lifts to the exact
    `.call none` arm of `inlineProgHOLCoreExact` under `crepProgToHOL`.
    Untagged Flapjack-specific infrastructure. -/
theorem crepProgToHOL_crepInlineCallBody_none {width : Nat} [NeZero width]
    (name : FunName) (arguments : List (CrepExp (BitVec width)))
    (argumentNames : List Nat) (body : CrepProg (BitVec width)) :
    crepProgToHOL (crepInlineCallBody none name arguments argumentNames body) =
      inlineTailHOLExact
        (argLoadHOLExact
          (genlistSuccAddHOLExact
            (max (((arguments.map crepExpToHOL).flatMap crepExpVarsHOL).foldl max 0)
              (argumentNames.foldl max 0))
            argumentNames.length)
          (arguments.map crepExpToHOL) argumentNames (crepProgToHOL body)) := by
  unfold crepInlineCallBody
  rw [crepProgToHOL_crepInlineTail, crepProgToHOL_crepArgLoad, crepInlineTmpNames_codec]

/-! ## Variable-occurrence and branch-return codec bridges

The executed inliner consults the variable-occurrence analysis `crepVarProg`,
its maximum `crepVmaxProg`, and the branch-return predicates `crepHasReturn`
and `crepNotBranchRet` on the production `CrepProg` carrier.  The exact
`inlineProgHOLCoreExact` instead consults the tagged exact ports
`crepVarProgHOLExact`, `crepVmaxProgHOLExact`, `hasReturnHOLExact` and
`notBranchRetHOLExact` on `CrepProgHOL`.  These helper declarations prove that
the executed analyses are the `crepProgToHOL` images of the exact ones, so the
call-arm guard and maximum computations agree under the codec.  They are
Flapjack-specific cross-representation facts with no cakeml HOL original, so
they carry no `@[hol]` tag. -/

/-- `crepExpVars` agrees with the exact `crepExpVarsHOL` under `crepExpToHOL`:
    a form of `crepExpVarsW_eq_crepExpVarsHOL_crepExpToHOL` with the production
    delegating definition on the left. -/
theorem crepExpVars_codec {width : Nat} [NeZero width] (expression : CrepExp (BitVec width)) :
    crepExpVars expression = crepExpVarsHOL (crepExpToHOL expression) :=
  crepExpVarsW_eq_crepExpVarsHOL_crepExpToHOL expression

/-- Executed `crepVarProg` agrees with the exact `crepVarProgHOLExact` under the
    `crepProgToHOL` codec. -/
theorem crepVarProg_codec {width : Nat} [NeZero width] (program : CrepProg (BitVec width)) :
    crepVarProg program = crepVarProgHOLExact (crepProgToHOL program) := by
  fun_induction crepVarProg program with
  | case1 name value body ih =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec, ih]
  | case2 name value =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec]
  | case3 names op arguments =>
      simp only [crepProgToHOL, crepVarProgHOLExact]
  | case4 address value =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec]
  | case5 address value =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec]
  | case6 address value =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec]
  | case7 address value =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec]
  | case8 first second ih1 ih2 =>
      simp only [crepProgToHOL, crepVarProgHOLExact, ih1, ih2]
  | case9 condition thenBranch elseBranch ih1 ih2 =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec, ih1, ih2]
  | case10 condition body ih =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec, ih]
  | case11 name arguments =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_flatMap_codec]
  | case12 names name arguments =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_flatMap_codec]
  | case13 names handler body name arguments ih =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_flatMap_codec, ih]
  | case14 function configuration configurationLength array arrayLength =>
      simp only [crepProgToHOL, crepVarProgHOLExact]
  | case15 values =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_flatMap_codec]
  | case16 operator name address =>
      simp only [crepProgToHOL, crepVarProgHOLExact, crepExpVars_codec]
  | case17 => simp only [crepProgToHOL, crepVarProgHOLExact]
  | case18 label => simp only [crepProgToHOL, crepVarProgHOLExact]
  | case19 label => simp only [crepProgToHOL, crepVarProgHOLExact]
  | case20 exception => simp only [crepProgToHOL, crepVarProgHOLExact]
  | case21 => simp only [crepProgToHOL, crepVarProgHOLExact]

/-- Executed `crepVmaxProg` agrees with the exact `crepVmaxProgHOLExact` under
    the codec. -/
theorem crepVmaxProg_codec {width : Nat} [NeZero width] (program : CrepProg (BitVec width)) :
    crepVmaxProg program = crepVmaxProgHOLExact (crepProgToHOL program) := by
  unfold crepVmaxProg crepVmaxProgHOLExact
  rw [crepVarProg_codec]

/-- Executed `crepHasReturn` agrees with the exact `hasReturnHOLExact` under the
    codec. -/
theorem crepHasReturn_codec {width : Nat} [NeZero width] :
    (program : CrepProg (BitVec width)) →
      crepHasReturn program = hasReturnHOLExact (crepProgToHOL program)
  | .skip => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .dec name value body => by
      simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
      exact crepHasReturn_codec body
  | .assign name value => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .primitive names operator args => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .store address value => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .store32 address value => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .storeByte address value => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .storeGlob address value => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .seq first second => by
      simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
      rw [crepHasReturn_codec first, crepHasReturn_codec second]
  | .ite condition thenBranch elseBranch => by
      simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
      rw [crepHasReturn_codec thenBranch, crepHasReturn_codec elseBranch]
  | .while condition body => by
      simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
      exact crepHasReturn_codec body
  | .break label => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .continue label => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .call none _ _ => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .call (some (_, none)) _ _ => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .call (some (_, some (_, handler))) _ _ => by
      simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
      exact crepHasReturn_codec handler
  | .extCall function configuration configurationLength array arrayLength =>
      by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .raise exception => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .return values => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .shMem operator name address => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]
  | .tick => by simp only [crepHasReturn, crepProgToHOL, hasReturnHOLExact]

/-- Executed `crepNotBranchRet` agrees with the exact `notBranchRetHOLExact`
    under the codec. -/
theorem crepNotBranchRet_codec {width : Nat} [NeZero width] :
    (program : CrepProg (BitVec width)) →
      crepNotBranchRet program = notBranchRetHOLExact (crepProgToHOL program)
  | .skip => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .dec _ _ body => by
      simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
      exact crepNotBranchRet_codec body
  | .assign name value => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .primitive names operator args => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .store address value => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .store32 address value => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .storeByte address value => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .storeGlob address value => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .seq first second => by
      simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
      rw [crepNotBranchRet_codec first, crepNotBranchRet_codec second]
  | .ite _ thenBranch elseBranch => by
      simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
      rw [crepHasReturn_codec thenBranch, crepHasReturn_codec elseBranch]
  | .while _ body => by
      simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
      rw [crepHasReturn_codec body]
  | .break label => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .continue label => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .call none _ _ => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .call (some (_, none)) _ _ => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .call (some (_, some (_, handler))) _ _ => by
      simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
      rw [crepHasReturn_codec handler]
  | .extCall function configuration configurationLength array arrayLength =>
      by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .raise exception => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .return values => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .shMem operator name address => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]
  | .tick => by simp only [crepNotBranchRet, crepProgToHOL, notBranchRetHOLExact]

/-- Executed inline call body with a `some (returnNames, none)` return shape lifts
    to the exact `some (returnNames, none)` arm computation under `crepProgToHOL`.
    Here the argument `body` plays the role of the exact `inlinedCallee` that the
    caller supplies (in the production recursion it is the `crepUnreachElim` result
    of the recursive inlining of the callee). -/
theorem crepProgToHOL_crepInlineCallBody_some_none {width : Nat} [NeZero width]
    (returnNames : List Nat) (name : FunName)
    (arguments : List (CrepExp (BitVec width)))
    (argumentNames : List Nat) (body : CrepProg (BitVec width)) :
    crepProgToHOL (crepInlineCallBody (some (returnNames, none)) name arguments
        argumentNames body) =
      (if !crepAllDistinct returnNames then
        CrepProgHOL.call (some (returnNames, none)) (ofString name)
          (arguments.map crepExpToHOL)
      else
        let maxArguments :=
          ((arguments.map crepExpToHOL).flatMap crepExpVarsHOL).foldl max 0
        let maxArgumentNames := argumentNames.foldl max 0
        let temporaryNames :=
          genlistSuccAddHOLExact (max maxArguments maxArgumentNames)
            argumentNames.length
        let maxReturnNames := returnNames.foldl max 0
        let maxInlinedCallee := crepVmaxProgHOLExact (crepProgToHOL body)
        let maxTemporaryNames := temporaryNames.foldl max 0
        let temporaryReturns :=
          genlistSuccAddHOLExact
            (max maxReturnNames (max maxInlinedCallee maxTemporaryNames))
            returnNames.length
        let transformedCallee :=
          if notBranchRetHOLExact (crepProgToHOL body) then
            .seq .tick (transformEocHOLExact temporaryReturns (crepProgToHOL body))
          else
            .while (.const 1)
              (transformBranchHOLExact 0 temporaryReturns (crepProgToHOL body))
        inlineNontailHOLExact transformedCallee returnNames temporaryReturns
          temporaryNames (arguments.map crepExpToHOL) argumentNames) := by
  simp only [crepInlineCallBody]
  by_cases hd : (!crepAllDistinct returnNames) = true
  · rw [if_pos hd, if_pos hd]
    simp only [crepProgToHOL]
  · rw [if_neg hd, if_neg hd]
    rw [crepInlineTmpNames_codec, crepVmaxProg_codec, crepNotBranchRet_codec]
    by_cases hbr : notBranchRetHOLExact (crepProgToHOL body) = true
    · rw [if_pos hbr, if_pos hbr]
      simp only [crepProgToHOL, crepProgToHOL_crepTransformEoc,
        crepProgToHOL_crepInlineNontail, genlistSuccAddHOLExact, Nat.add_assoc]
    · rw [if_neg hbr, if_neg hbr]
      simp only [crepProgToHOL, crepExpToHOL, crepProgToHOL_crepTransformBranch,
        crepProgToHOL_crepInlineNontail, genlistSuccAddHOLExact, Nat.add_assoc]

/-- The `ofString`/`toStringOfBytes` codec preserves Bool equality on
    byte-ranged names. -/
theorem beq_ofString_eq_ofString {s t : String}
    (hs : CrepNameRanged s) (ht : CrepNameRanged t) :
    (ofString s == ofString t) = (s == t) := by
  rw [beq_comm (ofString s) (ofString t), beq_ofString_eq ht,
      toStringOfBytes_ofString_of_bytes s hs, beq_comm t s]

/-- Production active-name membership after erasing `name` matches the exact
    finite-map lookup guarded by the same erase, under the `toStringOfBytes`
    codec. Introduced for the pending inline body-recursion relation, where the
    executable pass carries a list of inlineable entries together with an active
    name set while the exact core carries the `alistToFmapHOLExact` finite map. -/
theorem crepInlineActiveNames_erase_codec {width : Nat} [NeZero width] {α : Type}
    (bodyDecode : CrepProgHOL width → CrepProg α)
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width)))
    (name : FunName) (s : String) (hs : CrepNameRanged s) (hname : CrepNameRanged name) :
    ((crepInlineActiveNames (entries.map (fun e =>
        (toStringOfBytes e.1, (e.2.1, bodyDecode e.2.2))))).erase name).contains s =
      (((alistToFmapHOLExact entries).erase (ofString name)).lookup (ofString s)).isSome := by
  rw [Std.HashSet.contains_erase, crepInlineActiveNames_contains_eq,
      crepInlineLookup_codec bodyDecode entries s hs, Option.isSome_map,
      HolFiniteMapExact.lookup_erase,
      show (FDOMSUB (alistToFmapHOLExact entries).lookup (ofString name) (ofString s)) =
        FLOOKUP (FDOMSUB (alistToFmapHOLExact entries).lookup (ofString name)) (ofString s) from rfl,
      FLOOKUP_domsub, beq_ofString_eq_ofString hname hs]
  cases hb : (name == s) <;> simp_all [FLOOKUP]

def crepInlineCodecEntries {width : Nat} [NeZero width]
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width))) :
    List (CrepInlineEntry (BitVec width)) :=
  entries.map fun e => (toStringOfBytes e.1, (e.2.1, crepProgOfHOL e.2.2))

def crepProgNameRanged {width : Nat} [NeZero width] : CrepProg (BitVec width) → Prop
  | .skip => True
  | .dec _ _ body => crepProgNameRanged body
  | .assign _ _ => True
  | .primitive _ _ _ => True
  | .store _ _ => True
  | .store32 _ _ => True
  | .storeByte _ _ => True
  | .storeGlob _ _ => True
  | .seq first second => crepProgNameRanged first ∧ crepProgNameRanged second
  | .ite _ thenBranch elseBranch =>
      crepProgNameRanged thenBranch ∧ crepProgNameRanged elseBranch
  | .while _ body => crepProgNameRanged body
  | .break _ => True
  | .continue _ => True
  | .call none name _ => CrepNameRanged name
  | .call (some (_, none)) name _ => CrepNameRanged name
  | .call (some (_, some (_, body))) name _ => CrepNameRanged name ∧ crepProgNameRanged body
  | .extCall function _ _ _ _ => CrepNameRanged function
  | .raise _ => True
  | .return _ => True
  | .shMem _ _ _ => True
  | .tick => True

private theorem erase_active_contains {width : Nat} [NeZero width]
    (map : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (active : Std.HashSet FunName) (name s : FunName)
    (hactive : ∀ s, CrepNameRanged s → active.contains s = (map.lookup (ofString s)).isSome)
    (hname : CrepNameRanged name) (hs : CrepNameRanged s) :
    (active.erase name).contains s =
      ((map.erase (ofString name)).lookup (ofString s)).isSome := by
  rw [Std.HashSet.contains_erase, hactive s hs, HolFiniteMapExact.lookup_erase,
      show (FDOMSUB map.lookup (ofString name) (ofString s)) =
        FLOOKUP (FDOMSUB map.lookup (ofString name)) (ofString s) from rfl,
      FLOOKUP_domsub, beq_ofString_eq_ofString hname hs]
  by_cases hb : (name == s) = true <;> simp_all [FLOOKUP]

private theorem erase_active_lookup {width : Nat} [NeZero width]
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width)))
    (map : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (active : Std.HashSet FunName) (name : FunName)
    (hlookup : ∀ s, CrepNameRanged s → active.contains s = true →
      crepInlineLookup s (crepInlineCodecEntries entries) =
        (map.lookup (ofString s)).map (fun e => (e.1, crepProgOfHOL e.2)))
    (hname : CrepNameRanged name) :
    ∀ s, CrepNameRanged s → (active.erase name).contains s = true →
      crepInlineLookup s (crepInlineCodecEntries entries) =
        ((map.erase (ofString name)).lookup (ofString s)).map
          (fun e => (e.1, crepProgOfHOL e.2)) := by
  intro s hs hcont
  rw [Std.HashSet.contains_erase] at hcont
  rw [Bool.and_eq_true] at hcont
  obtain ⟨h1, h2⟩ := hcont
  rw [hlookup s hs h2, HolFiniteMapExact.lookup_erase,
      show (FDOMSUB map.lookup (ofString name) (ofString s)) =
        FLOOKUP (FDOMSUB map.lookup (ofString name)) (ofString s) from rfl,
      FLOOKUP_domsub, beq_ofString_eq_ofString hname hs]
  cases hb : (name == s) <;> simp_all [FLOOKUP]

private theorem erase_range {width : Nat} [NeZero width]
    (map : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (name : CrepInlineMapHOLName)
    (hrange : ∀ k v, map.lookup k = some v → crepProgNameRanged (crepProgOfHOL v.2)) :
    ∀ k v, (map.erase name).lookup k = some v → crepProgNameRanged (crepProgOfHOL v.2) := by
  intro k v h
  rw [HolFiniteMapExact.lookup_erase,
      show (FDOMSUB map.lookup name k) = FLOOKUP (FDOMSUB map.lookup name) k from rfl,
      FLOOKUP_domsub] at h
  by_cases hk : (name == k) = true
  · rw [hk] at h; simp at h
  · rw [Bool.not_eq_true] at hk
    rw [hk] at h; simp only [Bool.false_eq_true, if_false, FLOOKUP] at h
    exact hrange k v (by simpa using h)

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- Executed inliner recursion lifts to the exact tagged `inlineProgHOLCoreExact`
    under `crepProgToHOL`, carrying the finite-map, support and byte-range invariants
    through the recursive erase step.  This is the body-recursion core of the
    production/exact inline route relation (Flapjack-specific, no cakeml HOL original,
    hence untagged). -/
theorem crepProgToHOL_crepInlineProgRecursive {width : Nat} [NeZero width]
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width)))
    (active : Std.HashSet FunName) (program : CrepProg (BitVec width)) :
    ∀ (map : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
      (supportKeys : List CrepInlineMapHOLName)
      (support_spec : ∀ key, map.lookup key ≠ none → key ∈ supportKeys),
      (∀ s, CrepNameRanged s → active.contains s = (map.lookup (ofString s)).isSome) →
      (∀ s, CrepNameRanged s → active.contains s = true →
        crepInlineLookup s (crepInlineCodecEntries entries) =
          (map.lookup (ofString s)).map (fun e => (e.1, crepProgOfHOL e.2))) →
      (∀ k v, map.lookup k = some v → crepProgNameRanged (crepProgOfHOL v.2)) →
      crepProgNameRanged program →
      crepProgToHOL (crepInlineProgRecursive (crepInlineCodecEntries entries) active program) =
        inlineProgHOLCoreExact map supportKeys support_spec (crepProgToHOL program) := by
  fun_induction crepInlineProgRecursive (crepInlineCodecEntries entries) active program with
  | case1 active name value body ih =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      simp only [crepInlineProgRecursive, crepProgToHOL, inlineProgHOLCoreExact]
      rw [ih map supportKeys support_spec hactive hlookup hrange hprog]
  | case2 active first second ih1 ih2 =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      simp only [crepInlineProgRecursive, crepProgToHOL, inlineProgHOLCoreExact]
      rw [ih1 map supportKeys support_spec hactive hlookup hrange hprog.1,
          ih2 map supportKeys support_spec hactive hlookup hrange hprog.2]
  | case3 active condition thenBranch elseBranch ih1 ih2 =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      simp only [crepInlineProgRecursive, crepProgToHOL, inlineProgHOLCoreExact]
      rw [ih1 map supportKeys support_spec hactive hlookup hrange hprog.1,
          ih2 map supportKeys support_spec hactive hlookup hrange hprog.2]
  | case4 active condition body ih =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      simp only [crepInlineProgRecursive, crepProgToHOL, inlineProgHOLCoreExact]
      rw [ih map supportKeys support_spec hactive hlookup hrange hprog]
  | case5 active name arguments hmem hlookupNone =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      have hcont : active.contains name = true := Std.HashSet.mem_iff_contains.mp hmem
      have hmapEq := hlookup name hprog hcont
      rw [hlookupNone] at hmapEq
      have hmapNone : map.lookup (ofString name) = none := by
        cases hm : map.lookup (ofString name) with
        | none => rfl
        | some e => rw [hm] at hmapEq; simp at hmapEq
      have hc := hactive name hprog
      rw [hcont, hmapNone] at hc
      simp at hc
  | case6 active name arguments hmem argumentNames body hlookupSome body' snd hrec ih =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      have hcont : active.contains name = true := Std.HashSet.mem_iff_contains.mp hmem
      have hmapEq : (map.lookup (ofString name)).map (fun e => (e.1, crepProgOfHOL e.2)) =
          some (argumentNames, body) := by
        rw [← hlookup name hprog hcont]; exact hlookupSome
      obtain ⟨p, hmap, hdecode⟩ := Option.map_eq_some_iff.mp hmapEq
      have harg : argumentNames = p.1 := (Prod.ext_iff.mp hdecode).1.symm
      have hbody : body = crepProgOfHOL p.2 := (Prod.ext_iff.mp hdecode).2.symm
      cases harg
      cases hbody
      have hactive' : ∀ s, CrepNameRanged s →
          (active.erase name).contains s = ((map.erase (ofString name)).lookup (ofString s)).isSome :=
        fun s hs => erase_active_contains map active name s hactive hprog hs
      have hlookup' := erase_active_lookup entries map active name hlookup hprog
      have hrange' := erase_range map (ofString name) hrange
      have hbodyRange : crepProgNameRanged (crepProgOfHOL p.2) := hrange (ofString name) p hmap
      have hrecToHOL : crepProgToHOL
            (crepInlineProgRecursive (crepInlineCodecEntries entries) (active.erase name)
              (crepProgOfHOL p.2)) =
          inlineProgHOLCoreExact (map.erase (ofString name))
            (supportKeys.filter (fun k => k != ofString name))
            (HolFiniteMapExact.erase_support map supportKeys support_spec (ofString name))
            (crepProgToHOL (crepProgOfHOL p.2)) :=
        ih (map.erase (ofString name)) (supportKeys.filter (fun k => k != ofString name))
          (HolFiniteMapExact.erase_support map supportKeys support_spec (ofString name))
          hactive' hlookup' hrange' hbodyRange
      have hbody' : crepProgToHOL body' =
          (unreachElimHOLExact (inlineProgHOLCoreExact (map.erase (ofString name))
            (supportKeys.filter (fun k => k != ofString name))
            (HolFiniteMapExact.erase_support map supportKeys support_spec (ofString name))
            (crepProgToHOL (crepProgOfHOL p.2)))).1 := by
        have hun := crepProgToHOL_crepUnreachElim
          (crepInlineProgRecursive (crepInlineCodecEntries entries) (active.erase name)
            (crepProgOfHOL p.2))
        rw [hrec, hrecToHOL] at hun
        simpa only [Prod.fst] using congrArg Prod.fst hun
      rw [crepProgToHOL_crepInlineCallBody_none, hbody']
      simp only [crepProgToHOL, crepProgToHOL_crepProgOfHOL]
      rw [inlineProgHOLCoreExact_call_none, hmap]
  | case7 active name arguments hnot =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      have hcont : active.contains name = false := by
        cases h : active.contains name with
        | false => rfl
        | true => exact absurd (Std.HashSet.mem_iff_contains.mpr h) hnot
      have hmapEq := hactive name hprog
      rw [hcont] at hmapEq
      have hmapNone : map.lookup (ofString name) = none := by
        have h := hactive name hprog
        rw [hcont] at h
        exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp h.symm)
      simp only [crepInlineProgRecursive, dif_neg hnot, crepProgToHOL]
      rw [inlineProgHOLCoreExact_call_none, hmapNone]
  | case8 active returnNames name arguments hmem hlookupNone =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      have hcont : active.contains name = true := Std.HashSet.mem_iff_contains.mp hmem
      have hmapEq := hlookup name hprog hcont
      rw [hlookupNone] at hmapEq
      have hmapNone : map.lookup (ofString name) = none := by
        cases hm : map.lookup (ofString name) with
        | none => rfl
        | some e => rw [hm] at hmapEq; simp at hmapEq
      have hc := hactive name hprog
      rw [hcont, hmapNone] at hc
      simp at hc
  | case9 active returnNames name arguments hmem argumentNames body hlookupSome body' snd hrec ih =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      have hcont : active.contains name = true := Std.HashSet.mem_iff_contains.mp hmem
      have hmapEq : (map.lookup (ofString name)).map (fun e => (e.1, crepProgOfHOL e.2)) =
          some (argumentNames, body) := by
        rw [← hlookup name hprog hcont]; exact hlookupSome
      obtain ⟨p, hmap, hdecode⟩ := Option.map_eq_some_iff.mp hmapEq
      have harg : argumentNames = p.1 := (Prod.ext_iff.mp hdecode).1.symm
      have hbody : body = crepProgOfHOL p.2 := (Prod.ext_iff.mp hdecode).2.symm
      cases harg
      cases hbody
      have hactive' : ∀ s, CrepNameRanged s →
          (active.erase name).contains s = ((map.erase (ofString name)).lookup (ofString s)).isSome :=
        fun s hs => erase_active_contains map active name s hactive hprog hs
      have hlookup' := erase_active_lookup entries map active name hlookup hprog
      have hrange' := erase_range map (ofString name) hrange
      have hbodyRange : crepProgNameRanged (crepProgOfHOL p.2) := hrange (ofString name) p hmap
      have hrecToHOL : crepProgToHOL
            (crepInlineProgRecursive (crepInlineCodecEntries entries) (active.erase name)
              (crepProgOfHOL p.2)) =
          inlineProgHOLCoreExact (map.erase (ofString name))
            (supportKeys.filter (fun k => k != ofString name))
            (HolFiniteMapExact.erase_support map supportKeys support_spec (ofString name))
            (crepProgToHOL (crepProgOfHOL p.2)) :=
        ih (map.erase (ofString name)) (supportKeys.filter (fun k => k != ofString name))
          (HolFiniteMapExact.erase_support map supportKeys support_spec (ofString name))
          hactive' hlookup' hrange' hbodyRange
      have hbody' : crepProgToHOL body' =
          (unreachElimHOLExact (inlineProgHOLCoreExact (map.erase (ofString name))
            (supportKeys.filter (fun k => k != ofString name))
            (HolFiniteMapExact.erase_support map supportKeys support_spec (ofString name))
            (crepProgToHOL (crepProgOfHOL p.2)))).1 := by
        have hun := crepProgToHOL_crepUnreachElim
          (crepInlineProgRecursive (crepInlineCodecEntries entries) (active.erase name)
            (crepProgOfHOL p.2))
        rw [hrec, hrecToHOL] at hun
        simpa only [Prod.fst] using congrArg Prod.fst hun
      rw [crepProgToHOL_crepInlineCallBody_some_none, hbody']
      simp only [crepProgToHOL, crepProgToHOL_crepProgOfHOL]
      rw [inlineProgHOLCoreExact_call_returns, hmap]
  | case10 active returnNames name arguments hnot =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      have hcont : active.contains name = false := by
        cases h : active.contains name with
        | false => rfl
        | true => exact absurd (Std.HashSet.mem_iff_contains.mpr h) hnot
      have hmapEq := hactive name hprog
      rw [hcont] at hmapEq
      have hmapNone : map.lookup (ofString name) = none := by
        have h := hactive name hprog
        rw [hcont] at h
        exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp h.symm)
      simp only [crepInlineProgRecursive, dif_neg hnot, crepProgToHOL, inlineProgHOLCoreExact]
      rw [hmapNone]
      by_cases hg : (!crepAllDistinct returnNames) = true
      · simp only [hg, if_true]
      · simp only [hg, if_false]
        rfl
  | case11 active returnNames handler body name arguments ih =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      simp only [crepProgNameRanged] at hprog
      simp only [crepInlineProgRecursive, crepProgToHOL, inlineProgHOLCoreExact]
      rw [ih map supportKeys support_spec hactive hlookup hrange hprog.2]
  | case12 active program h1 h2 h3 h4 h5 h6 h7 =>
      intro map supportKeys support_spec hactive hlookup hrange hprog
      cases program with
      | dec name value body => exact absurd rfl (h1 name value body)
      | seq first second => exact absurd rfl (h2 first second)
      | ite condition thenBranch elseBranch => exact absurd rfl (h3 condition thenBranch elseBranch)
      | «while» condition body => exact absurd rfl (h4 condition body)
      | call ret name arguments =>
          cases ret with
          | none => exact absurd rfl (h5 name arguments)
          | some r =>
              cases r with
              | mk returnNames ropt =>
                  cases ropt with
                  | none => exact absurd rfl (h6 returnNames name arguments)
                  | some hb =>
                      obtain ⟨handler, body⟩ := hb
                      exact absurd rfl (h7 returnNames handler body name arguments)
      | _ => simp only [crepInlineProgRecursive, crepProgToHOL, inlineProgHOLCoreExact]

end CrepInlineRoute
end Flapjack
