module

public import Flapjack.Compiler.Backend.FlatElim.Reachability
public import Flapjack.Compiler.Backend.Semantics.FlatSem

@[expose] public section

/-! Global dependencies stored in flat-language values. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

mutual
/-- Global slots referenced by a flat value, including captured environments
and recursive function bodies. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_def"]
def findValueGlobals : FlatSem.Value → NumSet
  | .conv _ values => findValuesGlobals values
  | .closure ⟨bindings⟩ _ body => sptUnion (findBindingsGlobals bindings) (findLookups body)
  | .recclosure ⟨bindings⟩ funs _ => sptUnion (findBindingsGlobals bindings) (findGlobalsFuns destGlobalVarLookup funs)
  | .vectorv values => findValuesGlobals values
  | _ => .ln
termination_by value => sizeOf value

/-- List clause of the value-global analysis. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_def"]
def findValuesGlobals : List FlatSem.Value → NumSet
  | [] => .ln
  | value :: rest => sptUnion (findValueGlobals value) (findValuesGlobals rest)
termination_by values => sizeOf values

/-- Flapjack-specific traversal of captured bindings, rendering HOL's
`find_v_globalsL (MAP SND env.v)` without an intermediate list. It has no
separate HOL declaration; `findBindingsGlobals_eq_map` proves the equation. -/
def findBindingsGlobals : List (Flapjack.AstHOL.VarN × FlatSem.Value) → NumSet
  | [] => .ln
  | (_, value) :: rest => sptUnion (findValueGlobals value) (findBindingsGlobals rest)
termination_by bindings => sizeOf bindings
end

/-- The unit value refers to no global slots. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_Unitv"]
theorem findValueGlobals_unit : findValueGlobals FlatSem.unitValue = .ln := by
  simp [FlatSem.unitValue, findValueGlobals, findValuesGlobals]

/-- Captured-binding traversal agrees with the original mapped value list. -/
theorem findBindingsGlobals_eq_map (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) :
    findBindingsGlobals bindings = findValuesGlobals (bindings.map Prod.snd) := by
  induction bindings with
  | nil => simp [findBindingsGlobals, findValuesGlobals]
  | cons binding rest ih =>
    cases binding
    simp [findBindingsGlobals, findValuesGlobals, ih]

/-- Recursive-function traversal agrees with the original mapped body list. -/
theorem findFunctionGlobals_eq_map (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    findGlobalsFuns destGlobalVarLookup funs =
      findGlobalsList destGlobalVarLookup (funs.map (fun (_, _, body) => body)) := by
  induction funs with
  | nil => simp [findGlobalsFuns, findGlobalsList]
  | cons funSpec rest ih =>
    obtain ⟨_, _, _⟩ := funSpec
    simp [findGlobalsFuns, findGlobalsList, ih]

/-- Global dependencies reachable from all reference-store values. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_refs_globals_def"]
def findRefsGlobals : List (Flapjack.SemanticPrimitivesHOL.StoreValue FlatSem.Value) → NumSet
  | [] => .ln
  | .refv value :: rest => sptUnion (findValueGlobals value) (findRefsGlobals rest)
  | .varray values :: rest => sptUnion (findValuesGlobals values) (findRefsGlobals rest)
  | .thunk _ value :: rest => sptUnion (findValueGlobals value) (findRefsGlobals rest)
  | _ :: rest => findRefsGlobals rest

/-- Every reference, array and thunk stored in the list has globals within
    the set that bounds the entire reference-store analysis. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_refs_globals_MEM"]
theorem findRefsGlobals_mem (R : Nat → Prop) :
    ∀ (refs : List (StoreValue FlatSem.Value)) (_reachable : NumSet),
      (∀ key, sptMem key (findRefsGlobals refs) → R key) →
      (∀ value, .refv value ∈ refs → ∀ key, sptMem key (findValueGlobals value) → R key) ∧
      (∀ values, .varray values ∈ refs → ∀ key, sptMem key (findValuesGlobals values) → R key) ∧
      (∀ mode value, .thunk mode value ∈ refs → ∀ key, sptMem key (findValueGlobals value) → R key) := by
  intro refs
  induction refs with
  | nil => simp
  | cons ref rest ih =>
    intro reachable bounded
    have restBound : ∀ key, sptMem key (findRefsGlobals rest) → R key := by
      intro key found
      apply bounded key
      cases ref <;> simp_all [findRefsGlobals, sptMem_sptUnion]
    obtain ⟨refs, arrays, thunks⟩ := ih reachable restBound
    refine ⟨?_, ?_, ?_⟩
    · intro value member key found
      rcases List.mem_cons.mp member with equal | member
      · subst ref
        apply bounded key
        exact (sptMem_sptUnion _ _ _).mpr (Or.inl found)
      · exact refs value member key found
    · intro values member key found
      rcases List.mem_cons.mp member with equal | member
      · subst ref
        apply bounded key
        exact (sptMem_sptUnion _ _ _).mpr (Or.inl found)
      · exact arrays values member key found
    · intro mode value member key found
      rcases List.mem_cons.mp member with equal | member
      · subst ref
        apply bounded key
        exact (sptMem_sptUnion _ _ _).mpr (Or.inl found)
      · exact thunks mode value member key found

/-- Global dependencies in a flat local environment. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_env_globals_def"]
def findEnvGlobals (env : FlatSem.Environment FlatSem.Value) : NumSet :=
  findValuesGlobals (env.v.map Prod.snd)

/-- Global dependencies in a raised flat result. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_result_globals_def"]
def findResultGlobals : Option (Flapjack.SemanticPrimitivesHOL.ErrorResult FlatSem.Value) → NumSet
  | some (.raise value) => findValueGlobals value
  | _ => .ln

/-- Global dependencies in a primitive result, including successful values. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_sem_prim_res_globals_def"]
def findPrimitiveResultGlobals : Flapjack.SemanticPrimitivesHOL.Result (List FlatSem.Value) FlatSem.Value → NumSet
  | .err error => findResultGlobals (some error)
  | .val values => findValuesGlobals values

mutual
/-- Whether a flat value or a captured value contains dynamic Eval. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "v_has_Eval_def1"]
def valueHasEval : FlatSem.Value → Bool
  | .conv _ values => valuesHaveEval values
  | .closure ⟨bindings⟩ _ body => hasEval body || bindingsHaveEval bindings
  | .recclosure ⟨bindings⟩ funs _ => bindingsHaveEval bindings || hasEvalFuns funs
  | .vectorv values => valuesHaveEval values
  | _ => false
termination_by value => sizeOf value

/-- Flapjack-specific recursive implementation of the existential list traversal
in `valueHasEval`; it has no separate HOL declaration. -/
def valuesHaveEval : List FlatSem.Value → Bool
  | [] => false
  | value :: rest => valueHasEval value || valuesHaveEval rest
termination_by values => sizeOf values

/-- Flapjack-specific recursive implementation of the mapped existential
binding traversal in `valueHasEval`; it has no separate HOL declaration. -/
def bindingsHaveEval : List (Flapjack.AstHOL.VarN × FlatSem.Value) → Bool
  | [] => false
  | (_, value) :: rest => valueHasEval value || bindingsHaveEval rest
termination_by bindings => sizeOf bindings
end

/-- The unit value contains no dynamic Eval. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "v_has_Eval_Unitv"]
theorem valueHasEval_unit : valueHasEval FlatSem.unitValue = false := by
  simp [FlatSem.unitValue, valueHasEval, valuesHaveEval]

/-- The binding helper is the original mapped existential value test. -/
theorem bindingsHaveEval_eq_map (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) :
    bindingsHaveEval bindings = valuesHaveEval (bindings.map Prod.snd) := by
  induction bindings with
  | nil => simp [bindingsHaveEval, valuesHaveEval]
  | cons binding rest ih =>
    cases binding
    simp [bindingsHaveEval, valuesHaveEval, ih]

/-- The recursive-function helper is the original mapped body test. -/
theorem hasEvalFuns_eq_map (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    hasEvalFuns funs = (funs.map (fun (_, _, body) => body)).any hasEval := by
  induction funs with
  | nil => simp [hasEvalFuns]
  | cons funSpec rest ih =>
    obtain ⟨_, _, _⟩ := funSpec
    simp [hasEvalFuns, ih]

private theorem valuesHaveEval_eq_any (values : List FlatSem.Value) :
    valuesHaveEval values = values.any valueHasEval := by
  induction values with
  | nil => simp [valuesHaveEval]
  | cons value rest ih => simp [valuesHaveEval, ih]

/-- The eta-reduced constructor equations for the value Eval test. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "v_has_Eval_def"]
theorem valueHasEval_equations :
    (∀ (name : Flapjack.AstHOL.VarN) (env : FlatSem.Environment FlatSem.Value) (e : FlatLang.Exp),
      valueHasEval (.closure env name e) = (hasEval e || (env.v.map Prod.snd).any valueHasEval)) ∧
    (∀ (vl : List FlatSem.Value) (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)),
      valueHasEval (.conv stamp vl) = vl.any valueHasEval) ∧
    (∀ (name : Flapjack.AstHOL.VarN) (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
        (env : FlatSem.Environment FlatSem.Value),
      valueHasEval (.recclosure env funs name) =
        ((env.v.map Prod.snd).any valueHasEval || (funs.map (fun (_, _, body) => body)).any hasEval)) ∧
    (∀ vl : List FlatSem.Value, valueHasEval (.vectorv vl) = vl.any valueHasEval) ∧
    (∀ lit : Flapjack.AstHOL.Lit, valueHasEval (.litv lit) = false) ∧
    (∀ (address : Nat) (flag : Bool), valueHasEval (.loc flag address) = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name env e
    cases env
    simp [valueHasEval, bindingsHaveEval_eq_map, valuesHaveEval_eq_any]
  · intro vl stamp
    simp [valueHasEval, valuesHaveEval_eq_any]
  · intro name funs env
    cases env
    simp [valueHasEval, bindingsHaveEval_eq_map, valuesHaveEval_eq_any, hasEvalFuns_eq_map]
  · intro vl
    simp [valueHasEval, valuesHaveEval_eq_any]
  · intro lit
    simp [valueHasEval]
  · intro address flag
    simp [valueHasEval]

/-- Flapjack-specific abbreviation of the HOL subset of sparse-tree domains;
it has no separate HOL declaration. -/
def globalsWithin (globals reachable : NumSet) : Prop :=
  ∀ key, sptMem key globals → sptMem key reachable

/-- Reachability of a union is equivalent to reachability of both inputs. -/
theorem globalsWithin_union (left right reachable : NumSet) :
    globalsWithin (sptUnion left right) reachable ↔
      globalsWithin left reachable ∧ globalsWithin right reachable := by
  simp only [globalsWithin, sptMem_sptUnion]
  exact ⟨fun h => ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩,
    fun h k hk => hk.elim (h.1 k) (h.2 k)⟩

/-- Every member value's global dependencies occur in the list analysis. -/
theorem findValuesGlobals_member (values : List FlatSem.Value) (value : FlatSem.Value)
    (member : value ∈ values) (key : Nat) (found : sptMem key (findValueGlobals value)) :
    sptMem key (findValuesGlobals values) := by
  induction values with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    simp only [findValuesGlobals, sptMem_sptUnion]
    rcases member with rfl | member
    · exact Or.inl found
    · exact Or.inr (ih member)

/-- A list is reachable exactly when every member value is reachable. -/
theorem findValuesGlobals_within_iff (values : List FlatSem.Value) (reachable : NumSet) :
    globalsWithin (findValuesGlobals values) reachable ↔
      ∀ value ∈ values, globalsWithin (findValueGlobals value) reachable := by
  induction values with
  | nil => simp [findValuesGlobals, globalsWithin, sptMem, sptDomain]
  | cons value rest ih =>
    simp only [findValuesGlobals, globalsWithin_union, List.mem_cons, forall_eq_or_imp, ih]

/-- Replication introduces no dependencies beyond those of the repeated value. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globalsL_REPLICATE"]
theorem findValuesGlobals_replicate {α : Type} (n : Nat) (value : FlatSem.Value) (_vs : α) :
    globalsWithin (findValuesGlobals (List.replicate n value)) (findValueGlobals value) := by
  induction n with
  | zero => simp [findValuesGlobals, globalsWithin, sptMem, sptDomain]
  | succ n ih =>
    simp only [List.replicate_succ, findValuesGlobals, globalsWithin_union]
    exact ⟨fun _ h => h, ih⟩

/-- Replacing a list element with a reachable value preserves reachability. -/
theorem findValuesGlobals_set_within (values : List FlatSem.Value) (index : Nat)
    (value : FlatSem.Value) (reachable : NumSet)
    (old : globalsWithin (findValuesGlobals values) reachable)
    (new : globalsWithin (findValueGlobals value) reachable) :
    globalsWithin (findValuesGlobals (values.set index value)) reachable := by
  apply (findValuesGlobals_within_iff _ _).mpr
  intro item member
  rcases List.mem_or_eq_of_mem_set member with oldMember | rfl
  · exact (findValuesGlobals_within_iff _ _).mp old item oldMember
  · exact new

/-- An in-bounds list update preserves the original global-dependency bound. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globalsL_LUPDATE"]
theorem findValuesGlobals_LUPDATE (index : Nat) (values : List FlatSem.Value)
    (reachable : NumSet) (value : FlatSem.Value)
    (premises : index < values.length ∧ globalsWithin (findValuesGlobals values) reachable ∧
      globalsWithin (findValueGlobals value) reachable) :
    globalsWithin (findValuesGlobals (values.set index value)) reachable :=
  findValuesGlobals_set_within values index value reachable premises.2.1 premises.2.2

/-- Global dependencies held by a single store entry. -/
def storeValueGlobals : StoreValue FlatSem.Value → NumSet
  | .refv value | .thunk _ value => findValueGlobals value
  | .varray values => findValuesGlobals values
  | .w8array _ => .ln

/-- A store is reachable exactly when every entry's dependencies are reachable. -/
theorem findRefsGlobals_within_iff (refs : List (StoreValue FlatSem.Value)) (reachable : NumSet) :
    globalsWithin (findRefsGlobals refs) reachable ↔
      ∀ ref ∈ refs, globalsWithin (storeValueGlobals ref) reachable := by
  induction refs with
  | nil => simp [findRefsGlobals, globalsWithin, sptMem, sptDomain]
  | cons ref rest ih =>
    cases ref <;>
      simp only [findRefsGlobals, List.mem_cons, forall_eq_or_imp, storeValueGlobals,
        globalsWithin_union, ih]
    simp [globalsWithin, sptMem, sptDomain]

/-- Replacing a store entry with a reachable entry preserves reachability. -/
theorem findRefsGlobals_set_within (refs : List (StoreValue FlatSem.Value))
    (index : Nat) (value : StoreValue FlatSem.Value) (reachable : NumSet)
    (old : globalsWithin (findRefsGlobals refs) reachable)
    (new : globalsWithin (storeValueGlobals value) reachable) :
    globalsWithin (findRefsGlobals (refs.set index value)) reachable := by
  apply (findRefsGlobals_within_iff _ _).mpr
  intro ref member
  rcases List.mem_or_eq_of_mem_set member with oldMember | rfl
  · exact (findRefsGlobals_within_iff _ _).mp old ref oldMember
  · exact new

/-- Updating a store entry preserves the bound when the inserted value is
reachable; byte arrays add no value dependencies. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_refs_globals_LUPDATE"]
theorem findRefsGlobals_LUPDATE (reachable : NumSet) (refs : List (StoreValue FlatSem.Value))
    (index : Nat) (premises : index < refs.length ∧
      globalsWithin (findRefsGlobals refs) reachable) :
    (∀ value, globalsWithin (findValueGlobals value) reachable →
      globalsWithin (findRefsGlobals (refs.set index (.refv value))) reachable) ∧
    (∀ values, globalsWithin (findValuesGlobals values) reachable →
      globalsWithin (findRefsGlobals (refs.set index (.varray values))) reachable) ∧
    (∀ bytes, globalsWithin (findRefsGlobals (refs.set index (.w8array bytes))) reachable) ∧
    (∀ mode value, globalsWithin (findValueGlobals value) reachable →
      globalsWithin (findRefsGlobals (refs.set index (.thunk mode value))) reachable) := by
  obtain ⟨_, old⟩ := premises
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro value safe
    exact findRefsGlobals_set_within refs index (.refv value) reachable old safe
  · intro values safe
    exact findRefsGlobals_set_within refs index (.varray values) reachable old safe
  · intro bytes
    apply findRefsGlobals_set_within refs index (.w8array bytes) reachable old
    simp [storeValueGlobals, globalsWithin, sptMem, sptDomain]
  · intro mode value safe
    exact findRefsGlobals_set_within refs index (.thunk mode value) reachable old safe

end Flapjack.Compiler.Backend.FlatElim
