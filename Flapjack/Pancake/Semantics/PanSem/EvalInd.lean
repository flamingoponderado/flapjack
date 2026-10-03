import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
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
  apply ExpHOL.rec
    (motive_1 := fun e => ∀ s, P s e)
    (motive_2 := fun es => ∀ s a, a ∈ es → P s a)
    (motive_3 := fun fields => ∀ s a, a ∈ fields.map Prod.snd → P s a)
    (motive_4 := fun entry => ∀ s, P s entry.2)
    (t := e)
  · exact fun w s => hconst s w
  · intro kind name s
    cases kind
    · exact hlocal s name
    · exact hglobal s name
  · exact fun es ih s => hrstruct s es (ih s)
  · exact fun index e ih s => hrfield s index e (ih s)
  · intro name fields ih s
    apply hnstruct s name fields
    intro fieldNames fieldExps info fieldNames' fieldShapes a hunzip _ _ _ hm
    have he : fieldExps = fields.map Prod.snd := by
      simpa using congrArg Prod.snd hunzip
    exact ih s a (he ▸ hm)
  · exact fun name e ih s => hnfield s name e (ih s)
  · exact fun shape address ih s => hload s shape address (fun _ => ih s)
  · exact fun address ih s => hload32 s address (ih s)
  · exact fun address ih s => hloadByte s address (ih s)
  · exact fun operator es ih s => hop s operator es (ih s)
  · exact fun operator es ih s => hpanop s operator es (ih s)
  · exact fun operator left right ihl ihr s => hcmp s operator left right ⟨ihl s, ihr s⟩
  · exact fun operator left right ihl ihr s => hshift s operator left right ⟨ihl s, ihr s⟩
  · exact hbase
  · exact htop
  · exact hbytes
  · simp
  · intro head tail ihhead ihtail s a hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ihhead s
    · exact ihtail s a hm
  · simp
  · intro head tail ihhead ihtail s a hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ihhead s
    · exact ihtail s a hm
  · exact fun name e ih s => ih s
end Flapjack.Pancake.Semantics.PanSem.EvalInd
