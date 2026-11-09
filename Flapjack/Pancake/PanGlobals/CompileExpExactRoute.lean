module

public import Flapjack.Pancake.PanGlobals.CompileExpExact
public import Flapjack.Pancake.PanLang.Exp

@[expose] public section

/-!
Finite-support adapter between the production PanGlobals pass context and the
reviewed exact `compileExpExactHOL` carrier.

`pan_globals$compile_exp_def` is ported at the exact carrier in
`Flapjack/Pancake/PanGlobals/CompileExpExact.lean`. The production
`GlobalPassContext.globals` is an association list (`InfoMap`), so it carries
finite support; `PanGlobalsContextExact.ofPass` below reconstructs the exact
finite-support context from it, decoding production `String` names through
`NameRanged` and shapes through `shapeToHOL`, together with its lookup lemmas.

This is Flapjack infrastructure, not a HOL declaration, so nothing here carries
an `@[hol]` tag. -/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ExpHOL expToHOL expOfHOL varExpHOL ExpByteRanged ListExpByteRanged NameRanged
    shapeToHOL shapeOfHOL ShapeByteRanged ProgHOL progToHOL progOfHOL ProgByteRanged
    DeclByteRanged FunDeclByteRanged)

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

/-!
### Routing the executed decl/prog compilers through `compileExpExactHOL`
The production `compileDecsCake`/`compileProgCake` bodies remain
unchanged. The kernel-checked equalities below show the routed siblings
compute exactly the production output on byte-ranged input, so rewiring
the executed entry point keeps the observable compiler result. Flapjack
routing infrastructure (untagged).
-/

/-- Flapjack routing infrastructure (untagged). -/
def GlobalContextListShapesByteRanged [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) : Prop :=
  ∀ entry ∈ context.globals, ShapeByteRanged entry.2.1

/-- Prepending a byte-ranged shape preserves the list-indexed shape invariant.
    Flapjack routing infrastructure (untagged). -/
theorem globalContextListShapesByteRanged_update [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) (name : String) (shape : Shape)
    (address : BitVec width)
    (hcontext : GlobalContextListShapesByteRanged context)
    (hshape : ShapeByteRanged shape) :
    GlobalContextListShapesByteRanged
      { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address } := by
  intro entry hmem
  rw [List.mem_cons] at hmem
  rcases hmem with hhead | htail
  · subst hhead
    exact hshape
  · exact hcontext entry htail

/-- The exact finite-map lookup induced by a production `InfoMap` is the
    `shapeToHOL` image of the same production lookup for byte-ranged names.
    This is the carrier relation needed by the global `VarKind` clauses of the
    compiler commute proof; it is Flapjack infrastructure, not a HOL
    declaration. -/
theorem panGlobalsContextExact_ofPass_lookup [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (name : String)
    (hname : NameRanged name) :
    (PanGlobalsContextExact.ofPass context).globals.lookup (ofString name) =
      (lookupInfo name context.globals).map
        (fun entry => (shapeToHOL entry.1, entry.2)) := by
  simp [PanGlobalsContextExact.ofPass,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname]

end Flapjack
