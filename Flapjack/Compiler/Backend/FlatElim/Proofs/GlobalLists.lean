module

public import Flapjack.Compiler.Backend.FlatElim.Proofs.ValueGlobals
public import Flapjack.Misc.Sptree.UnionAlgebra
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Global-dependency properties of expression, value and store lists. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- Lookup dependencies distribute over appended expression lists. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_lookupsL_APPEND"]
theorem findLookupsList_append (left right : List FlatLang.Exp) :
    findGlobalsList destGlobalVarLookup (left ++ right) =
      sptUnion (findGlobalsList destGlobalVarLookup left) (findGlobalsList destGlobalVarLookup right) := by
  induction left with
  | nil => simp [findGlobalsList, sptUnion]
  | cons first rest ih => simp [findGlobalsList, ih, sptUnion_assoc]

/-- Value dependencies distribute over appended value lists. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globalsL_APPEND"]
theorem findValuesGlobals_append (left right : List FlatSem.Value) :
    findValuesGlobals (left ++ right) = sptUnion (findValuesGlobals left) (findValuesGlobals right) := by
  induction left with
  | nil => simp [findValuesGlobals, sptUnion]
  | cons first rest ih => simp [findValuesGlobals, ih, sptUnion_assoc]

/-- Reversing an expression list preserves its lookup dependencies. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_lookupsL_REVERSE"]
theorem findLookupsList_reverse (expressions : List FlatLang.Exp) :
    findGlobalsList destGlobalVarLookup expressions =
      findGlobalsList destGlobalVarLookup expressions.reverse := by
  induction expressions with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.reverse_cons, findLookupsList_append, findGlobalsList, ih]
    have empty : sptUnion (findGlobals destGlobalVarLookup first) .ln = findGlobals destGlobalVarLookup first := by
      cases h : findGlobals destGlobalVarLookup first <;> simp [sptUnion]
    simpa only [empty] using
      (sptUnion_numSet_sym (findGlobals destGlobalVarLookup first) (findGlobalsList destGlobalVarLookup rest.reverse))

/-- Reversing a value list preserves its global dependencies. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globalsL_REVERSE"]
theorem findValuesGlobals_reverse (values : List FlatSem.Value) :
    findValuesGlobals values = findValuesGlobals values.reverse := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.reverse_cons, findValuesGlobals_append, findValuesGlobals, ih]
    have empty : sptUnion (findValueGlobals first) .ln = findValueGlobals first := by
      cases h : findValueGlobals first <;> simp [sptUnion]
    simpa [empty] using (sptUnion_numSet_sym (findValueGlobals first) (findValuesGlobals rest.reverse))

/-- Store dependencies distribute over appended reference lists. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_refs_globals_APPEND"]
theorem findRefsGlobals_append (refs new : List (StoreValue FlatSem.Value)) :
    findRefsGlobals (refs ++ new) = sptUnion (findRefsGlobals refs) (findRefsGlobals new) := by
  induction refs with
  | nil => simp [findRefsGlobals, sptUnion]
  | cons first rest ih => cases first <;> simp [findRefsGlobals, ih, sptUnion_assoc]

/-- A binding's value dependencies occur in the analysis of all bindings. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globalsL_MEM"]
theorem findValuesGlobals_map_snd_mem {α : Type} (k : α) (v : FlatSem.Value)
    (vs : List (α × FlatSem.Value)) (member : (k, v) ∈ vs) :
    ∀ key, sptMem key (findValueGlobals v) →
      sptMem key (findValuesGlobals (vs.map Prod.snd)) := by
  exact findValuesGlobals_member (vs.map Prod.snd) v (List.mem_map.mpr ⟨(k, v), member, rfl⟩)

/-- Every in-bounds value's dependencies occur in the list analysis. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globalsL_EL"]
theorem findValuesGlobals_el (n : Nat) (values : List FlatSem.Value) (bound : n < values.length) :
    ∀ key, sptMem key (findValueGlobals (@Flapjack.holEl FlatSem.Value ⟨FlatSem.unitValue⟩ n values)) →
      sptMem key (findValuesGlobals values) := by
  rw [@Flapjack.holEl_eq_getElem FlatSem.Value ⟨FlatSem.unitValue⟩ n values bound]
  exact findValuesGlobals_member values values[n] (List.getElem_mem bound)

/-- An in-bounds value inherits any bound on the list's global dependencies. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globalsL_EL_trans"]
theorem findValuesGlobals_el_trans (n : Nat) (values : List FlatSem.Value) (R : Nat → Prop)
    (premises : n < values.length ∧ ∀ key, sptMem key (findValuesGlobals values) → R key) :
    ∀ key, sptMem key (findValueGlobals (@Flapjack.holEl FlatSem.Value ⟨FlatSem.unitValue⟩ n values)) → R key := by
  intro key member
  exact premises.2 key (findValuesGlobals_el n values premises.1 key member)

/-- A bounded store analysis bounds the dependencies of its indexed entry. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_refs_globals_EL"]
theorem findRefsGlobals_el (n : Nat) (refs : List (StoreValue FlatSem.Value)) (R : Nat → Prop)
    (premises : n < refs.length ∧ ∀ key, sptMem key (findRefsGlobals refs) → R key) :
    (∀ value, @Flapjack.holEl (StoreValue FlatSem.Value) ⟨.refv FlatSem.unitValue⟩ n refs = .refv value →
      ∀ key, sptMem key (findValueGlobals value) → R key) ∧
    (∀ values, @Flapjack.holEl (StoreValue FlatSem.Value) ⟨.refv FlatSem.unitValue⟩ n refs = .varray values →
      ∀ key, sptMem key (findValuesGlobals values) → R key) ∧
    (∀ mode value, @Flapjack.holEl (StoreValue FlatSem.Value) ⟨.refv FlatSem.unitValue⟩ n refs = .thunk mode value →
      ∀ key, sptMem key (findValueGlobals value) → R key) := by
  obtain ⟨bound, bounded⟩ := premises
  have member : @Flapjack.holEl (StoreValue FlatSem.Value) ⟨.refv FlatSem.unitValue⟩ n refs ∈ refs := by
    rw [@Flapjack.holEl_eq_getElem (StoreValue FlatSem.Value) ⟨.refv FlatSem.unitValue⟩ n refs bound]
    exact List.getElem_mem bound
  obtain ⟨refBound, arrayBound, thunkBound⟩ := findRefsGlobals_mem R refs .ln bounded
  exact ⟨fun value eq => refBound value (eq ▸ member),
    fun values eq => arrayBound values (eq ▸ member),
    fun mode value eq => thunkBound mode value (eq ▸ member)⟩

end Flapjack.Compiler.Backend.FlatElim
