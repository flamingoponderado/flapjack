import Flapjack.Compiler.Backend.FlatElim.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Pattern matching is preserved by the flat-elimination state relation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Pattern matching observes the state only through the reference store.
This is a Flapjack helper for the original state-relation theorem. -/
theorem pmatch_refs_eq {C F : Type} (first second : FlatSem.State C F)
    (refs : first.refs = second.refs) :
    (∀ pattern value bindings, FlatSem.pmatch first pattern value bindings =
      FlatSem.pmatch second pattern value bindings) ∧
    (∀ patterns values bindings, FlatSem.pmatchList first patterns values bindings =
      FlatSem.pmatchList second patterns values bindings) := by
  have one : ∀ pattern : FlatLang.Pat, ∀ value bindings,
      FlatSem.pmatch first pattern value bindings = FlatSem.pmatch second pattern value bindings := by
    apply FlatLang.Pat.rec
      (motive_1 := fun pattern => ∀ value bindings,
        FlatSem.pmatch first pattern value bindings = FlatSem.pmatch second pattern value bindings)
      (motive_2 := fun patterns => ∀ values bindings,
        FlatSem.pmatchList first patterns values bindings = FlatSem.pmatchList second patterns values bindings)
    case pany => intros; simp [FlatSem.pmatch]
    case pvar => intros; simp [FlatSem.pmatch]
    case plit => intro lit value bindings; cases value <;> simp [FlatSem.pmatch]
    case pcon =>
      intro stamp patterns ih value bindings
      cases value <;> simp [FlatSem.pmatch]
      case conv actual values =>
        split <;> simp_all
    case pref =>
      intro pattern ih value bindings
      cases value <;> simp [FlatSem.pmatch]
      case loc flag index =>
        simp only [refs]
        cases storeLookup index second.refs <;> simp_all
    case pas =>
      intro pattern name ih value bindings
      simpa [FlatSem.pmatch] using ih value ((name, value) :: bindings)
    case nil => intro values bindings; cases values <;> simp [FlatSem.pmatchList]
    case cons =>
      intro pattern patterns ihHead ihTail values bindings
      cases values with
      | nil => simp [FlatSem.pmatchList]
      | cons value values =>
        simp only [FlatSem.pmatchList, ihHead value bindings]
        cases FlatSem.pmatch second pattern value bindings <;> simp_all
  refine ⟨one, ?_⟩
  intro patterns
  induction patterns with
  | nil => intro values bindings; cases values <;> simp [FlatSem.pmatchList]
  | cons pattern patterns ih =>
    intro values bindings
    cases values with
    | nil => simp [FlatSem.pmatchList]
    | cons value values =>
      simp only [FlatSem.pmatchList, one pattern value bindings]
      cases FlatSem.pmatch second pattern value bindings <;> simp_all

/-- Related elimination states produce the same single-pattern and
pattern-list results, with the original conjunct quantification. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_state_rel_pmatch"]
theorem flatStateRel_pmatch {C F : Type} (reachable : NumSet) (removed : FlatSem.State C F) :
    (∀ source pattern value bindings, flatStateRel reachable source removed →
      FlatSem.pmatch removed pattern value bindings = FlatSem.pmatch source pattern value bindings) ∧
    (∀ source patterns values bindings, flatStateRel reachable source removed →
      FlatSem.pmatchList removed patterns values bindings = FlatSem.pmatchList source patterns values bindings) := by
  constructor
  · intro source pattern value bindings related
    exact (pmatch_refs_eq removed source related.2.1.symm).1 pattern value bindings
  · intro source patterns values bindings related
    exact (pmatch_refs_eq removed source related.2.1.symm).2 patterns values bindings

/-- Selecting the first matching expression row is unchanged by elimination. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_state_rel_pmatch_rows"]
theorem flatStateRel_pmatchRows {C F : Type} (reachable : NumSet)
    (source removed : FlatSem.State C F) (rows : List (FlatLang.Pat × FlatLang.Exp)) (value : FlatSem.Value)
    (related : flatStateRel reachable source removed) :
    FlatSem.pmatchRows rows removed value = FlatSem.pmatchRows rows source value := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨pattern, expr⟩ := row
    simp only [FlatSem.pmatchRows, (flatStateRel_pmatch reachable removed).1 source pattern value [] related, ih]

/-- A selected match row belongs to the original row list. -/
theorem pmatchRows_selected_mem {C F : Type} (rows : List (FlatLang.Pat × FlatLang.Exp))
    (state : FlatSem.State C F) (value : FlatSem.Value) (bindings : List (VarN × FlatSem.Value))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (selected : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body)) :
    (pattern, body) ∈ rows := by
  induction rows with
  | nil => simp [FlatSem.pmatchRows] at selected
  | cons row rest ih =>
    obtain ⟨p, e⟩ := row
    cases found : FlatSem.pmatch state p value [] with
    | typeError => simp [FlatSem.pmatchRows, found] at selected
    | noMatch =>
      exact List.mem_cons_of_mem _ (ih (by simpa [FlatSem.pmatchRows, found] using selected))
    | «match» first =>
      cases tail : FlatSem.pmatchRows rest state value with
      | typeError => simp [FlatSem.pmatchRows, found, tail] at selected
      | noMatch =>
        simp [FlatSem.pmatchRows, found, tail] at selected
        rcases selected with ⟨_, rfl, rfl⟩
        simp
      | «match» tailResult =>
        simp [FlatSem.pmatchRows, found, tail] at selected
        rcases selected with ⟨_, rfl, rfl⟩
        simp

/-- A member expression's global lookups occur in the list analysis. -/
theorem findLookupsList_member (body : FlatLang.Exp) (bodies : List FlatLang.Exp)
    (member : body ∈ bodies) (key : Nat) (found : sptMem key (findLookups body)) :
    sptMem key (findGlobalsList destGlobalVarLookup bodies) := by
  induction bodies with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    simp only [findGlobalsList, sptMem_sptUnion]
    rcases member with rfl | member
    · exact Or.inl found
    · exact Or.inr (ih member)

/-- A selected pattern row cannot introduce a lookup outside the reachable
set when every row body has already been analysed. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "pmatch_rows_find_lookups"]
theorem pmatchRows_findLookups {C F R : Type} (rows : List (FlatLang.Pat × FlatLang.Exp))
    (state : FlatSem.State C F) (value : FlatSem.Value) (bindings : List (VarN × FlatSem.Value))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp) (reachable : Spt R)
    (selected : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body))
    (bounded : ∀ key, sptMem key (findGlobalsList destGlobalVarLookup (rows.map Prod.snd)) → sptMem key reachable) :
    ∀ key, sptMem key (findLookups body) → sptMem key reachable := by
  intro key found
  apply bounded key
  apply findLookupsList_member body _ _ key found
  exact List.mem_map.mpr ⟨(pattern, body), pmatchRows_selected_mem rows state value bindings pattern body selected, rfl⟩

end Flapjack.Compiler.Backend.FlatElim
