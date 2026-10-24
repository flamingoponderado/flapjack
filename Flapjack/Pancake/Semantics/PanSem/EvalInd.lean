module

public import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

@[expose] public section
namespace Flapjack.Pancake.Semantics.PanSem.EvalInd
open Flapjack Flapjack.Pancake.PanLang

/-- Imported canonical state roundtrip for the finite-map representation.
Flapjack infrastructure with no independent HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Full original faithful evaluator induction principle, including the original
NStruct UNZIP/lookup/name guards and Load shape guard. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "eval_ind"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalIndExact {width : Nat} {σ : Type} [NeZero width]
    (P : PanSemStateFiniteExact width σ → ExpHOL width → Prop)
    (hconst : ∀ s w, P s (.const w))
    (hlocal : ∀ s name, P s (.var .local name))
    (hglobal : ∀ s name, P s (.var .global name))
    (hrstruct : ∀ s es, (∀ a ∈ es, P s a) → P s (.rstruct es))
    (hrfield : ∀ s index e, P s e → P s (.rfield index e))
    (hnstruct : ∀ s name fields,
      (∀ fieldNames fieldExps (info : StructInfoHOLExact) fieldNames' fieldShapes a,
        (fieldNames, fieldExps) = fields.unzip →
        s.structs.findSome? (fun entry => if entry.1 = name then some entry.2 else none) = some info →
        (fieldNames', fieldShapes) = info.fields.unzip →
        fieldNames' = fieldNames → a ∈ fieldExps → P s a) → P s (.nstruct name fields))
    (hnfield : ∀ s name e, P s e → P s (.nfield name e))
    (hload : ∀ s shape address,
      (isWfShapeExactHOL s.structs shape = true → P s address) → P s (.load shape address))
    (hload32 : ∀ s address, P s address → P s (.load32 address))
    (hloadByte : ∀ s address, P s address → P s (.loadByte address))
    (hop : ∀ s operator es, (∀ a ∈ es, P s a) → P s (.op operator es))
    (hpanop : ∀ s operator es, (∀ a ∈ es, P s a) → P s (.panop operator es))
    (hcmp : ∀ s operator left right, P s left ∧ P s right → P s (.cmp operator left right))
    (hshift : ∀ s operator left right, P s left ∧ P s right → P s (.shift operator left right))
    (hbase : ∀ s, P s .baseAddr)
    (htop : ∀ s, P s .topAddr)
    (hbytes : ∀ s, P s .bytesInWord) :
    ∀ s e, P s e := by
  intro s e
  fun_induction expOfHOL e with
  | case1 w => exact hconst s w
  | case2 kind name =>
      cases kind with
      | «local» => exact hlocal s name
      | global => exact hglobal s name
  | case3 es ih => exact hrstruct s es ih
  | case4 index e ih => exact hrfield s index e ih
  | case5 name fields ih =>
      apply hnstruct s name fields
      intro fieldNames fieldExps info fieldNames' fieldShapes a hunzip _ _ _ hm
      have he : fieldExps = fields.map Prod.snd := by
        simpa using congrArg Prod.snd hunzip
      obtain ⟨⟨name, value⟩, hfield, rfl⟩ := List.mem_map.mp (he ▸ hm)
      exact ih (name, value) hfield
  | case6 name e ih => exact hnfield s name e ih
  | case7 shape address ih => exact hload s shape address (fun _ => ih)
  | case8 address ih => exact hload32 s address ih
  | case9 address ih => exact hloadByte s address ih
  | case10 operator es ih => exact hop s operator es ih
  | case11 operator es ih => exact hpanop s operator es ih
  | case12 operator left right ihLeft ihRight => exact hcmp s operator left right ⟨ihLeft, ihRight⟩
  | case13 operator left right ihLeft ihRight => exact hshift s operator left right ⟨ihLeft, ihRight⟩
  | case14 => exact hbase s
  | case15 => exact htop s
  | case16 => exact hbytes s
end Flapjack.Pancake.Semantics.PanSem.EvalInd
