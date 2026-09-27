import Flapjack.Pancake.PanGlobals.CompileExpExact

/-!
Finite-support routing infrastructure between the executed PanGlobals
`compileExpCake` chain and the reviewed exact `compileExpExactHOL`.

`pan_globals$compile_exp_def` is ported at the exact carrier in
`Flapjack/Pancake/PanGlobals/CompileExpExact.lean`, but the executed
`compileDecsCake`/`compileProgCake`/`compileExpCake` chain still computes the
production String-backed function.  The production `GlobalPassContext.globals`
is an association list (`InfoMap`), so it does carry finite support; the adapter
`PanGlobalsContextExact.ofPass` below reconstructs the exact finite-support
context from it, decoding production `String` names through `NameRanged` and
shapes through `shapeToHOL`.

The kernel-checked equality `compileExpCake_ofPass_eq` then routes the executed
expression compiler on that production context through the reviewed
`compileExpExactHOL` under the byte-range premise the parser supplies:
`compileExpCake (cakeContextOfPass context) e = expOfHOL (compileExpExactHOL
(ofPass context) (expToHOL e))`.

This is Flapjack routing infrastructure, not a HOL declaration, so nothing here
carries an `@[hol]` tag.  It is also *not* textual routing: the production
`compileDecsCake`/`compileProgCake`/`compileExpCake` bodies are unchanged and
still compute the production function directly.  A body-level route is blocked
because those functions are total over arbitrary `String` (so they cannot
discharge the `ExpByteRanged`/`NameRanged` premise the codec needs inside their
bodies) and because `CakeContext.globals` erases the finite-support structure
(`α → Option β`) that the exact `HolFiniteMapExact` field requires.  The
remaining production routing is tracked by `flapjack-pxn.18.3.5.8.29`. -/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ExpHOL expToHOL expOfHOL ExpByteRanged ListExpByteRanged NameRanged
    shapeToHOL shapeOfHOL ShapeByteRanged)

/-- `lookupInfo` returns `some` only for a key that occurs in the association
    list.  Used to build the finite-support witness of the exact context from
    the production `InfoMap`.  Flapjack infrastructure (untagged). -/
theorem lookupInfo_exists_of_ne_none [BEq String] [LawfulBEq String] {α : Type}
    (key : String) : (entries : List (String × α)) →
      lookupInfo key entries ≠ none → ∃ entry ∈ entries, entry.1 = key := by
  intro entries
  induction entries with
  | nil => intro h; simp [lookupInfo] at h
  | cons head tail ih =>
      intro h
      obtain ⟨candidate, value⟩ := head
      simp only [lookupInfo] at h
      split at h
      · rename_i hcond
        exact ⟨(candidate, value), by simp, beq_iff_eq.mp hcond⟩
      · obtain ⟨entry, hmem, hkey⟩ := ih h
        exact ⟨entry, by simp [hmem], hkey⟩

/-- The value `lookupInfo` returns belongs to the association list (after
    re-associating its key).  Flapjack infrastructure (untagged). -/
theorem lookupInfo_eq_some_mem [BEq String] [LawfulBEq String] {α : Type}
    (key : String) : (entries : List (String × α)) → {value : α} →
      lookupInfo key entries = some value → (key, value) ∈ entries := by
  intro entries
  induction entries with
  | nil => intro value h; simp [lookupInfo] at h
  | cons head tail ih =>
      intro value h
      obtain ⟨candidate, v⟩ := head
      simp only [lookupInfo] at h
      split at h
      · rename_i hcond
        have hv : v = value := Option.some.inj h
        subst hv
        have hce : candidate = key := beq_iff_eq.mp hcond
        subst hce
        simp
      · exact List.mem_cons_of_mem _ (ih h)

namespace PanGlobalsContextExact

/-- Finite-support exact `pan_globals` context induced by the production
    `GlobalPassContext` association list.  Lookup decodes the `MlS` key through
    `toStringOfBytes` and maps each payload shape with `shapeToHOL`; the finite
    support is the image under `ofString` of the production `InfoMap` keys.
    Flapjack adapter infrastructure (untagged), the production-to-exact
    direction of `cakeContextOfExact`. -/
def ofPass [BEq String] [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) : PanGlobalsContextExact width where
  globals :=
    { lookup := fun name =>
        (lookupInfo (toStringOfBytes name) context.globals).map
          (fun entry => (shapeToHOL entry.1, entry.2))
      finiteSupport := by
        refine ⟨context.globals.map (fun entry => ofString entry.1), ?_⟩
        intro name hlookup
        have hne : lookupInfo (toStringOfBytes name) context.globals ≠ none := by
          intro hnone
          rw [hnone, Option.map_none] at hlookup
          exact hlookup rfl
        obtain ⟨entry, hmem, hkey⟩ :=
          lookupInfo_exists_of_ne_none (toStringOfBytes name) context.globals hne
        rw [List.mem_map]
        exact ⟨entry, hmem, by rw [hkey, ofString_toStringOfBytes]⟩ }
  globalsSize := context.globalsSize
  maxGlobalsSize := context.maxGlobalsSize

/-- Lookup of `ofPass` exposes the production `InfoMap` search and the shape
    encoding.  Flapjack infrastructure (untagged). -/
@[simp] theorem ofPass_globals_lookup [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width] (context : GlobalPassContext (BitVec width)) (name : MlS) :
    (ofPass context).globals.lookup name =
      (lookupInfo (toStringOfBytes name) context.globals).map
        (fun entry => (shapeToHOL entry.1, entry.2)) := rfl

end PanGlobalsContextExact

open PanGlobalsContextExact

/-- Looking up a key in the association list returns an entry whose shape is in
    the list; on a byte-ranged list the shape decode of its `shapeToHOL` image
    is the identity.  Flapjack infrastructure (untagged). -/
theorem lookupInfo_decode_shape_eq [BEq String] [LawfulBEq String] {width : Nat}
    (key : String) (entries : List (String × (Shape × BitVec width)))
    (hshapes : ∀ entry ∈ entries, ShapeByteRanged entry.2.1) :
    (lookupInfo key entries).map (fun entry => (shapeOfHOL (shapeToHOL entry.1), entry.2))
      = lookupInfo key entries := by
  cases h : lookupInfo key entries with
  | none => simp only [Option.map_none]
  | some entry =>
      obtain ⟨shape, address⟩ := entry
      have hmem : (key, (shape, address)) ∈ entries := lookupInfo_eq_some_mem key entries h
      have hshape : ShapeByteRanged shape := hshapes (key, (shape, address)) hmem
      simp only [Option.map_some]
      rw [Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL shape hshape]

/-- The exact context extracted from a production `GlobalPassContext` decodes,
    on byte-ranged keys, to the same production `CakeContext` produced by
    `cakeContextOfPass`, provided the stored shapes are byte-ranged.  Flapjack
    routing infrastructure (untagged). -/
theorem cakeContextOfExact_ofPass_globals [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width] (context : GlobalPassContext (BitVec width))
    (hshapes : ∀ entry ∈ context.globals, ShapeByteRanged entry.2.1)
    (key : String) (hkey : NameRanged key) :
    (cakeContextOfExact (ofPass context)).globals key
      = (cakeContextOfPass context).globals key := by
  show ((lookupInfo (toStringOfBytes (ofString key)) context.globals).map
      (fun entry => (shapeToHOL entry.1, entry.2))).map
        (fun entry => (shapeOfHOL entry.1, entry.2))
      = lookupInfo key context.globals
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes key hkey,
    Option.map_map]
  exact lookupInfo_decode_shape_eq key context.globals hshapes

/-- The executed `compileExpCake` is insensitive to replacing the
    `cakeContextOfPass` view of a byte-ranged production context by the exact
    `cakeContextOfExact (ofPass context)` view.  Flapjack routing infrastructure
    (untagged). -/
theorem compileExpCake_cakeContextOfExact_ofPass [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (hshapes : ∀ entry ∈ context.globals, ShapeByteRanged entry.2.1) :
    (expression : Exp (BitVec width)) → ExpByteRanged expression →
      compileExpCake (cakeContextOfExact (ofPass context)) expression
        = compileExpCake (cakeContextOfPass context) expression :=
  Flapjack.Exp.rec
    (motive_1 := fun expression =>
      ExpByteRanged expression →
        compileExpCake (cakeContextOfExact (ofPass context)) expression
          = compileExpCake (cakeContextOfPass context) expression)
    (motive_2 := fun expressions =>
      ListExpByteRanged expressions →
        compileExpCake.compileExpCakeList (cakeContextOfExact (ofPass context)) expressions
          = compileExpCake.compileExpCakeList (cakeContextOfPass context) expressions)
    (motive_3 := fun _ => True)
    (motive_4 := fun _ => True)
    (fun _value _ => by simp only [compileExpCake])
    (fun kind name hname => by
      cases kind with
      | «local» => simp only [compileExpCake]
      | global =>
          simp only [compileExpCake, FLOOKUP]
          rw [cakeContextOfExact_ofPass_globals context hshapes name hname])
    (fun expressions ih hexpressions => by
      simp only [compileExpCake]
      rw [ih hexpressions])
    (fun index value ih hvalue => by
      simp only [compileExpCake]
      rw [ih hvalue])
    (fun _name _fields _ih _ => by simp only [compileExpCake])
    (fun _name _value _ih _ => by simp only [compileExpCake])
    (fun _shape address ih hload => by
      obtain ⟨_hshape, haddress⟩ := hload
      simp only [compileExpCake]
      rw [ih haddress])
    (fun address ih haddress => by
      simp only [compileExpCake]
      rw [ih haddress])
    (fun address ih haddress => by
      simp only [compileExpCake]
      rw [ih haddress])
    (fun _operator args ih hargs => by
      simp only [compileExpCake]
      rw [ih hargs])
    (fun _operator args ih hargs => by
      simp only [compileExpCake]
      rw [ih hargs])
    (fun _operator left right ihl ihr hcmp => by
      obtain ⟨hl, hr⟩ := hcmp
      simp only [compileExpCake]
      rw [ihl hl, ihr hr])
    (fun _operator left right ihl ihr hshift => by
      obtain ⟨hl, hr⟩ := hshift
      simp only [compileExpCake]
      rw [ihl hl, ihr hr])
    (fun _ => by simp only [compileExpCake])
    (fun _ => by
      simp only [compileExpCake, PanGlobalsContextExact.cakeContextOfExact, ofPass,
        cakeContextOfPass])
    (fun _ => by simp only [compileExpCake])
    (fun _ => by simp only [compileExpCake.compileExpCakeList])
    (fun head tail ihHead ihTail hlist => by
      obtain ⟨hhead, htail⟩ := hlist
      simp only [compileExpCake.compileExpCakeList]
      rw [ihHead hhead, ihTail htail])
    True.intro
    (fun _ _ _ _ => True.intro)
    (fun _ _ _ => True.intro)

/-- Routing equality: on the production `cakeContextOfPass` view of a byte-ranged
    `GlobalPassContext`, the executed `compileExpCake` computes exactly the
    `expOfHOL` image of the reviewed exact `compileExpExactHOL` run on the exact
    finite-support context `ofPass context`.  This is Flapjack routing
    infrastructure (untagged); it does not change the production function body,
    which remains total over arbitrary `String`. -/
theorem compileExpCake_ofPass_eq [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (hshapes : ∀ entry ∈ context.globals, ShapeByteRanged entry.2.1)
    (expression : Exp (BitVec width)) (hranged : ExpByteRanged expression) :
    compileExpCake (cakeContextOfPass context) expression
      = expOfHOL (compileExpExactHOL (ofPass context) (expToHOL expression)) := by
  rw [← compileExpCake_cakeContextOfExact (ofPass context) expression hranged]
  exact (compileExpCake_cakeContextOfExact_ofPass context hshapes expression hranged).symm

end Flapjack
