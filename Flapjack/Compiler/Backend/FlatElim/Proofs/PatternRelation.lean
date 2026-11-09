import Flapjack.Compiler.Backend.FlatProps.PatternMatch
import Flapjack.Compiler.Backend.FlatElim.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Pattern matching is preserved by the flat-elimination state relation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

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
    exact FlatProps.pmatch_state.1 source pattern value bindings removed _ ⟨rfl, related.2.1⟩
  · intro source patterns values bindings related
    exact FlatProps.pmatch_state.2 source patterns values bindings removed _ ⟨rfl, related.2.1⟩

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

/-- A member expression's global lookups occur in the list analysis. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_lookupsL_MEM"]
theorem findLookupsList_member (body : FlatLang.Exp) (bodies : List FlatLang.Exp)
    : body ∈ bodies → ∀ key, sptMem key (findLookups body) →
      sptMem key (findGlobalsList destGlobalVarLookup bodies) := by
  intro member key found
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
    (premises : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body) ∧
      ∀ key, sptMem key (findGlobalsList destGlobalVarLookup (rows.map Prod.snd)) → sptMem key reachable) :
    ∀ key, sptMem key (findLookups body) → sptMem key reachable := by
  obtain ⟨selected, bounded⟩ := premises
  intro key found
  apply bounded key
  apply findLookupsList_member body _ _ key found
  exact List.mem_map.mpr ⟨(pattern, body), (FlatProps.pmatchRows_imp_pmatch rows state value bindings pattern body selected).2, rfl⟩

/-- Pattern environments use the same analysis as the original mapped list. -/
def bindingsWithin (bindings : List (VarN × FlatSem.Value)) (reachable : NumSet) : Prop :=
  globalsWithin (findValuesGlobals (bindings.map Prod.snd)) reachable

/-- Extending an environment adds exactly the new value's globals. -/
theorem bindingsWithin_cons (name : VarN) (value : FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (reachable : NumSet) :
    bindingsWithin ((name, value) :: bindings) reachable ↔
      globalsWithin (findValueGlobals value) reachable ∧ bindingsWithin bindings reachable := by
  simp [bindingsWithin, findValuesGlobals, globalsWithin_union]

/-- A successful match preserves the reachability bound on bindings. -/
theorem pmatchReachable_aux {C F : Type} (state : FlatSem.State C F) (reachable : NumSet) :
    (∀ pattern value bindings result, FlatSem.pmatch state pattern value bindings = .match result →
      globalsWithin (findValueGlobals value) reachable → bindingsWithin bindings reachable →
      globalsWithin (findRefsGlobals state.refs) reachable → bindingsWithin result reachable) ∧
    (∀ patterns values bindings result, FlatSem.pmatchList state patterns values bindings = .match result →
      globalsWithin (findValuesGlobals values) reachable → bindingsWithin bindings reachable →
      globalsWithin (findRefsGlobals state.refs) reachable → bindingsWithin result reachable) := by
  have one : ∀ pattern : FlatLang.Pat, ∀ value bindings result,
      FlatSem.pmatch state pattern value bindings = .match result →
      globalsWithin (findValueGlobals value) reachable → bindingsWithin bindings reachable →
      globalsWithin (findRefsGlobals state.refs) reachable → bindingsWithin result reachable := by
    apply FlatLang.Pat.rec
      (motive_1 := fun pattern => ∀ value bindings result,
        FlatSem.pmatch state pattern value bindings = .match result →
        globalsWithin (findValueGlobals value) reachable → bindingsWithin bindings reachable →
        globalsWithin (findRefsGlobals state.refs) reachable → bindingsWithin result reachable)
      (motive_2 := fun patterns => ∀ values bindings result,
        FlatSem.pmatchList state patterns values bindings = .match result →
        globalsWithin (findValuesGlobals values) reachable → bindingsWithin bindings reachable →
        globalsWithin (findRefsGlobals state.refs) reachable → bindingsWithin result reachable)
    case pany => intros; simp_all [FlatSem.pmatch]
    case pvar =>
      intro name value bindings result matched safe env store
      simp [FlatSem.pmatch] at matched
      subst result
      exact (bindingsWithin_cons name value bindings reachable).mpr ⟨safe, env⟩
    case plit =>
      intro lit value bindings result matched safe env store
      cases value <;> simp_all [FlatSem.pmatch]
      case litv actual =>
        split at matched <;> try simp_all
        split at matched <;> simp_all
    case pcon =>
      intro stamp patterns ih value bindings result matched safe env store
      cases value <;> simp [FlatSem.pmatch] at matched
      case conv actual values =>
        split at matched
        · split at matched
          · exact ih values bindings result matched (by simpa [findValueGlobals] using safe) env store
          · contradiction
        · contradiction
    case pref =>
      intro pattern ih value bindings result matched safe env store
      cases value <;> simp [FlatSem.pmatch] at matched
      case loc flag index =>
        cases lookup : storeLookup index state.refs with
        | none => simp [lookup] at matched
        | some ref =>
          cases ref <;> simp [lookup] at matched
          case refv v =>
            apply ih v bindings result matched
            · intro key found
              exact (findRefsGlobals_mem (fun n => sptMem n reachable) state.refs .ln store).1 v
                (List.mem_of_getElem? (by simpa [storeLookup] using lookup)) key found
            · exact env
            · exact store
    case pas =>
      intro pattern name ih value bindings result matched safe env store
      exact ih value ((name, value) :: bindings) result (by simpa [FlatSem.pmatch] using matched)
        safe ((bindingsWithin_cons name value bindings reachable).mpr ⟨safe, env⟩) store
    case nil =>
      intro values bindings result matched safe env store
      cases values <;> simp_all [FlatSem.pmatchList]
    case cons =>
      intro pattern patterns ihHead ihTail values bindings result matched safe env store
      cases values with
      | nil => simp [FlatSem.pmatchList] at matched
      | cons value values =>
        have parts : globalsWithin (findValueGlobals value) reachable ∧
            globalsWithin (findValuesGlobals values) reachable :=
          (globalsWithin_union _ _ _).mp (by simpa [findValuesGlobals] using safe)
        cases head : FlatSem.pmatch state pattern value bindings with
        | typeError => simp [FlatSem.pmatchList, head] at matched
        | noMatch =>
          cases tail : FlatSem.pmatchList state patterns values bindings <;>
            simp [FlatSem.pmatchList, head, tail] at matched
        | «match» next =>
          exact ihTail values next result (by simpa [FlatSem.pmatchList, head] using matched)
            parts.2 (ihHead value bindings next head parts.1 env store) store
  refine ⟨one, ?_⟩
  intro patterns
  induction patterns with
  | nil => intro values bindings result matched safe env store; cases values <;> simp_all [FlatSem.pmatchList]
  | cons pattern patterns ih =>
    intro values bindings result matched safe env store
    cases values with
    | nil => simp [FlatSem.pmatchList] at matched
    | cons value values =>
      have parts : globalsWithin (findValueGlobals value) reachable ∧
          globalsWithin (findValuesGlobals values) reachable :=
        (globalsWithin_union _ _ _).mp (by simpa [findValuesGlobals] using safe)
      cases head : FlatSem.pmatch state pattern value bindings with
      | typeError => simp [FlatSem.pmatchList, head] at matched
      | noMatch =>
        cases tail : FlatSem.pmatchList state patterns values bindings <;>
          simp [FlatSem.pmatchList, head, tail] at matched
      | «match» next =>
        exact ih values next result (by simpa [FlatSem.pmatchList, head] using matched)
          parts.2 (one pattern value bindings next head parts.1 env store) store

/-- Matched bindings do not refer to globals outside the reachable set. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "pmatch_Match_reachable"]
theorem pmatch_Match_reachable {C F : Type} :
    (∀ (state : FlatSem.State C F) pattern value bindings result reachable,
      FlatSem.pmatch state pattern value bindings = .match result ∧
      globalsWithin (findValueGlobals value) reachable ∧ bindingsWithin bindings reachable ∧
      globalsWithin (findRefsGlobals state.refs) reachable → bindingsWithin result reachable) ∧
    (∀ (state : FlatSem.State C F) patterns values bindings result reachable,
      FlatSem.pmatchList state patterns values bindings = .match result ∧
      globalsWithin (findValuesGlobals values) reachable ∧ bindingsWithin bindings reachable ∧
      globalsWithin (findRefsGlobals state.refs) reachable → bindingsWithin result reachable) := by
  constructor
  · intro state pattern value bindings result reachable ⟨matched, valueClosed, bindingsClosed, refsClosed⟩
    exact (pmatchReachable_aux state reachable).1 pattern value bindings result matched valueClosed bindingsClosed refsClosed
  · intro state patterns values bindings result reachable ⟨matched, valuesClosed, bindingsClosed, refsClosed⟩
    exact (pmatchReachable_aux state reachable).2 patterns values bindings result matched valuesClosed bindingsClosed refsClosed

/-- Flapjack-specific abbreviation for every value being Eval-free; HOL uses
the corresponding `EVERY` expression and has no separate declaration. -/
def valuesNoEval (values : List FlatSem.Value) : Prop :=
  ∀ value ∈ values, valueHasEval value = false

/-- Replacing a list element with an Eval-free value preserves the invariant. -/
theorem valuesNoEval_set (values : List FlatSem.Value) (index : Nat) (value : FlatSem.Value)
    (old : valuesNoEval values) (new : valueHasEval value = false) :
    valuesNoEval (values.set index value) := by
  intro item member
  rcases List.mem_or_eq_of_mem_set member with oldMember | rfl
  · exact old item oldMember
  · exact new

/-- Flapjack-specific abbreviation for Eval-free bindings; HOL uses an `EVERY`
expression over the mapped values and has no separate declaration. -/
def bindingsNoEval (bindings : List (VarN × FlatSem.Value)) : Prop :=
  ∀ binding ∈ bindings, valueHasEval binding.2 = false

/-- The recursive Boolean traversal agrees with its member-wise form. -/
theorem valuesHaveEval_eq_false_iff (values : List FlatSem.Value) :
    valuesHaveEval values = false ↔ valuesNoEval values := by
  induction values with
  | nil => simp [valuesHaveEval, valuesNoEval]
  | cons value rest ih =>
    simp [valuesHaveEval, valuesNoEval] at ih ⊢
    intro _
    exact ih

/-- A successful match preserves the absence of dynamic evaluation. -/
theorem pmatchNoEval_aux {C F : Type} (state : FlatSem.State C F) :
    (∀ pattern value bindings result, FlatSem.pmatch state pattern value bindings = .match result →
      valueHasEval value = false → storeHasNoEval state.refs → bindingsNoEval bindings →
      bindingsNoEval result) ∧
    (∀ patterns values bindings result, FlatSem.pmatchList state patterns values bindings = .match result →
      valuesNoEval values → storeHasNoEval state.refs → bindingsNoEval bindings →
      bindingsNoEval result) := by
  have one : ∀ pattern : FlatLang.Pat, ∀ value bindings result,
      FlatSem.pmatch state pattern value bindings = .match result →
      valueHasEval value = false → storeHasNoEval state.refs → bindingsNoEval bindings →
      bindingsNoEval result := by
    apply FlatLang.Pat.rec
      (motive_1 := fun pattern => ∀ value bindings result,
        FlatSem.pmatch state pattern value bindings = .match result →
        valueHasEval value = false → storeHasNoEval state.refs → bindingsNoEval bindings →
        bindingsNoEval result)
      (motive_2 := fun patterns => ∀ values bindings result,
        FlatSem.pmatchList state patterns values bindings = .match result →
        valuesNoEval values → storeHasNoEval state.refs → bindingsNoEval bindings →
        bindingsNoEval result)
    case pany => intros; simp_all [FlatSem.pmatch]
    case pvar =>
      intro name value bindings result matched safe store env
      simp [FlatSem.pmatch] at matched
      subst result
      simpa [bindingsNoEval] using And.intro safe env
    case plit =>
      intro lit value bindings result matched safe store env
      cases value <;> simp_all [FlatSem.pmatch]
      case litv actual =>
        split at matched <;> try simp_all
        split at matched <;> simp_all
    case pcon =>
      intro stamp patterns ih value bindings result matched safe store env
      cases value <;> simp [FlatSem.pmatch] at matched
      case conv actual values =>
        split at matched
        · split at matched
          · exact ih values bindings result matched
              ((valuesHaveEval_eq_false_iff values).mp (by simpa [valueHasEval] using safe)) store env
          · contradiction
        · contradiction
    case pref =>
      intro pattern ih value bindings result matched safe store env
      cases value <;> simp [FlatSem.pmatch] at matched
      case loc flag index =>
        cases lookup : storeLookup index state.refs with
        | none => simp [lookup] at matched
        | some ref =>
          cases ref <;> simp [lookup] at matched
          case refv v =>
            apply ih v bindings result matched
            · exact store _ (List.mem_of_getElem? (by simpa [storeLookup] using lookup)) v (by simp [FlatProps.storeValueValues])
            · exact store
            · exact env
    case pas =>
      intro pattern name ih value bindings result matched safe store env
      apply ih value ((name, value) :: bindings) result (by simpa [FlatSem.pmatch] using matched) safe store
      simpa [bindingsNoEval] using And.intro safe env
    case nil =>
      intro values bindings result matched safe store env
      cases values <;> simp_all [FlatSem.pmatchList]
    case cons =>
      intro pattern patterns ihHead ihTail values bindings result matched safe store env
      cases values with
      | nil => simp [FlatSem.pmatchList] at matched
      | cons value values =>
        have headSafe : valueHasEval value = false := safe value (by simp)
        have tailSafe : valuesNoEval values := by
          intro v member
          exact safe v (by simp [member])
        cases head : FlatSem.pmatch state pattern value bindings with
        | typeError => simp [FlatSem.pmatchList, head] at matched
        | noMatch =>
          cases tail : FlatSem.pmatchList state patterns values bindings <;>
            simp [FlatSem.pmatchList, head, tail] at matched
        | «match» next =>
          apply ihTail values next result (by simpa [FlatSem.pmatchList, head] using matched) tailSafe store
          exact ihHead value bindings next head headSafe store env
  refine ⟨one, ?_⟩
  intro patterns
  induction patterns with
  | nil => intro values bindings result matched safe store env; cases values <;> simp_all [FlatSem.pmatchList]
  | cons pattern patterns ih =>
    intro values bindings result matched safe store env
    cases values with
    | nil => simp [FlatSem.pmatchList] at matched
    | cons value values =>
      have headSafe : valueHasEval value = false := safe value (by simp)
      have tailSafe : valuesNoEval values := by
        intro v member
        exact safe v (by simp [member])
      cases head : FlatSem.pmatch state pattern value bindings with
      | typeError => simp [FlatSem.pmatchList, head] at matched
      | noMatch =>
        cases tail : FlatSem.pmatchList state patterns values bindings <;>
          simp [FlatSem.pmatchList, head, tail] at matched
      | «match» next =>
        apply ih values next result (by simpa [FlatSem.pmatchList, head] using matched) tailSafe store
        exact one pattern value bindings next head headSafe store env

/-- Successful pattern matching preserves the absence of Eval in all bindings. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "pmatch_not_has_Eval"]
theorem pmatch_not_has_Eval {C F : Type} :
    (∀ (state : FlatSem.State C F) pattern value bindings result,
      FlatSem.pmatch state pattern value bindings = .match result ∧
      valueHasEval value = false ∧ storeHasNoEval state.refs ∧ bindingsNoEval bindings →
      bindingsNoEval result) ∧
    (∀ (state : FlatSem.State C F) patterns values bindings result,
      FlatSem.pmatchList state patterns values bindings = .match result ∧
      valuesNoEval values ∧ storeHasNoEval state.refs ∧ bindingsNoEval bindings →
      bindingsNoEval result) := by
  constructor
  · intro state pattern value bindings result ⟨matched, valueSafe, refsSafe, bindingsSafe⟩
    exact (pmatchNoEval_aux state).1 pattern value bindings result matched valueSafe refsSafe bindingsSafe
  · intro state patterns values bindings result ⟨matched, valuesSafe, refsSafe, bindingsSafe⟩
    exact (pmatchNoEval_aux state).2 patterns values bindings result matched valuesSafe refsSafe bindingsSafe

/-- The selected row's environment satisfies both invariants needed by the
flat-elimination evaluation simulation. This combines the original matching
lemmas with the row-selection definition. -/
theorem pmatchRows_selected_invariants {C F : Type} (rows : List (FlatLang.Pat × FlatLang.Exp))
    (state : FlatSem.State C F) (value : FlatSem.Value) (bindings : List (VarN × FlatSem.Value))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp) (reachable : NumSet)
    (selected : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body))
    (valueSafe : valueHasEval value = false) (storeSafe : storeHasNoEval state.refs)
    (valueReachable : globalsWithin (findValueGlobals value) reachable)
    (storeReachable : globalsWithin (findRefsGlobals state.refs) reachable) :
    bindingsNoEval bindings ∧ bindingsWithin bindings reachable := by
  have matched := (FlatProps.pmatchRows_imp_pmatch rows state value bindings pattern body selected).1
  constructor
  · exact pmatch_not_has_Eval.1 state pattern value [] bindings
      ⟨matched, valueSafe, storeSafe, by simp [bindingsNoEval]⟩
  · exact pmatch_Match_reachable.1 state pattern value [] bindings reachable
      ⟨matched, valueReachable, by simp [bindingsWithin, globalsWithin, findValuesGlobals, sptMem, sptDomain],
        storeReachable⟩

end Flapjack.Compiler.Backend.FlatElim
