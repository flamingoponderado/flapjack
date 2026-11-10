module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.FreeVariables.Original
public import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ShiftedEnv
public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Mathlib.Data.List.Forall2
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.FreeVariables


@[expose] public section

/-! Candidate value and environment relations for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

mutual
/-- Relate source and annotated closure values. HOL's nested list relation is
factored into the mutually inductive `FunctionsRel`, characterized by
`functionsRel_iff` below. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_rel"
  (nested_list_rel_as_mutual := [FunctionsRel])]
inductive ValueRel : Value → Value → Prop where
  | number (value : Int) : ValueRel (.number value) (.number value)
  | word64 (value : BitVec 64) : ValueRel (.word64 value) (.word64 value)
  | block (tag : Nat) (left right : List Value) :
      List.Forall₂ ValueRel left right → ValueRel (.block tag left) (.block tag right)
  | byteVector (bytes : List (BitVec 8)) : ValueRel (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) : ValueRel (.refPtr flag address) (.refPtr flag address)
  | closure (location : Option Nat) (args nextArgs env nextEnv : List Value)
      (arity m : Nat) (body nextBody : ClosLang.Exp) (index : Spt Nat) :
      shiftSource (altFreeSource [body]).1 m arity index = [nextBody] →
      (∀ n, altFvSource n [body] = true ∧ arity ≤ n → EnvOk m 0 index env nextEnv (n - arity)) →
      everyFnVarsNone [body] → env.length = m → List.Forall₂ ValueRel args nextArgs →
      ValueRel (.closure location args env arity body) (.closure location nextArgs nextEnv arity nextBody)
  | recclosure (location : Option Nat) (args nextArgs env nextEnv : List Value)
      (functions nextFunctions : List (Nat × ClosLang.Exp)) (index : Nat) :
      FunctionsRel env nextEnv functions.length functions nextFunctions →
      List.Forall₂ ValueRel args nextArgs → index < functions.length →
      ValueRel (.recclosure location args env functions index)
        (.recclosure location nextArgs nextEnv nextFunctions index)

/-- Pointwise relation on recursive function bundles with a fixed bundle
length and shared captured environments. -/
inductive FunctionsRel : List Value → List Value → Nat →
    List (Nat × ClosLang.Exp) → List (Nat × ClosLang.Exp) → Prop where
  | nil (env nextEnv : List Value) (count : Nat) : FunctionsRel env nextEnv count [] []
  | cons (env nextEnv : List Value) (count arity m : Nat) (body nextBody : ClosLang.Exp)
      (index : Spt Nat) (functions nextFunctions : List (Nat × ClosLang.Exp)) :
      shiftSource (altFreeSource [body]).1 m (count + arity) index = [nextBody] →
      (∀ n, altFvSource n [body] = true ∧ arity + count ≤ n →
        EnvOk m 0 index env nextEnv (n - (arity + count))) →
      everyFnVarsNone [body] → env.length = m →
      FunctionsRel env nextEnv count functions nextFunctions →
      FunctionsRel env nextEnv count ((arity, body) :: functions) ((arity, nextBody) :: nextFunctions)

/-- Relate an environment slot through a compacting sparse map. Slots beyond
the tracked source environment impose no value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_rel"
  (nested_list_rel_as_mutual := [FunctionsRel])]
inductive EnvOk : Nat → Nat → Spt Nat → List Value → List Value → Nat → Prop where
  | outside (m l : Nat) (index : Spt Nat) (env nextEnv : List Value) (n : Nat) :
      l + m ≤ n → EnvOk m l index env nextEnv n
  | local (m l : Nat) (index : Spt Nat) (env nextEnv : List Value) (n : Nat) :
      n < l → ValueRel (@Flapjack.holEl Value ⟨unitValue⟩ n env) (@Flapjack.holEl Value ⟨unitValue⟩ n nextEnv) →
      n < env.length → n < nextEnv.length → EnvOk m l index env nextEnv n
  | captured (m l : Nat) (index : Spt Nat) (env nextEnv : List Value) (n compact : Nat) :
      l ≤ n → n < l + m → n < l + m → sptLookup (n - l) index = some compact →
      n < env.length → l + compact < nextEnv.length →
      ValueRel (@Flapjack.holEl Value ⟨unitValue⟩ n env) (@Flapjack.holEl Value ⟨unitValue⟩ (l + compact) nextEnv) →
      EnvOk m l index env nextEnv n
end

/-- Primitive numeric and byte-vector values relate only to themselves. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_rel_Number"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem valueRel_primitive (x : Value) (i : Int) (ws : List (BitVec 8)) (w : BitVec 64) :
    (ValueRel x (.number i) ↔ x = .number i) ∧
    (ValueRel (.number i) x ↔ x = .number i) ∧
    (ValueRel (.byteVector ws) x ↔ x = .byteVector ws) ∧
    (ValueRel x (.word64 w) ↔ x = .word64 w) ∧
    (ValueRel (.word64 w) x ↔ x = .word64 w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> constructor
  all_goals intro h
  all_goals first | (cases h; rfl) | (subst x; constructor)

/-- Related boolean values are equal in either direction. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_rel_Boolv"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem valueRel_bool (x : Value) (b : Bool) :
    (ValueRel x (boolValue b) ↔ x = boolValue b) ∧
      (ValueRel (boolValue b) x ↔ x = boolValue b) := by
  cases b <;> simp only [boolValue, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> constructor <;> intro h
  all_goals first | (cases h with | block _ _ _ rel => cases rel; rfl) | (subst x; exact .block _ [] [] .nil)

/-- Related unit values are equal in either direction. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_rel_Unit"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem valueRel_unit (x : Value) :
    (ValueRel x unitValue ↔ x = unitValue) ∧
      (ValueRel unitValue x ↔ x = unitValue) := by
  simp only [unitValue]
  constructor <;> constructor <;> intro h
  all_goals first | (cases h with | block _ _ _ rel => cases rel; rfl) | (subst x; exact .block _ [] [] .nil)

/-- Every set of variables is valid in an empty source environment. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem envSetDefault (vars : Set Nat) (targetEnv : List Value) :
    vars ⊆ {n | EnvOk 0 0 .ln [] targetEnv n} := by
  intro n _
  exact .outside 0 0 .ln [] targetEnv n (Nat.zero_le n)

/-- The inductive recursive-bundle relation is exactly the pointwise list
relation used in the source definition. -/
theorem functionsRel_iff (env nextEnv : List Value) (count : Nat)
    (functions nextFunctions : List (Nat × ClosLang.Exp)) :
    FunctionsRel env nextEnv count functions nextFunctions ↔
      List.Forall₂ (fun left right => ∃ m i,
        right.1 = left.1 ∧
        shiftSource (altFreeSource [left.2]).1 m (count + left.1) i = [right.2] ∧
        (∀ n, altFvSource n [left.2] = true ∧ left.1 + count ≤ n →
          EnvOk m 0 i env nextEnv (n - (left.1 + count))) ∧
        everyFnVarsNone [left.2] ∧ env.length = m) functions nextFunctions := by
  constructor
  · intro related
    induction functions generalizing nextFunctions with
    | nil => cases related; exact .nil
    | cons entry functions ih =>
      cases related with
      | cons _ _ _ arity m body nextBody index _ _ shifted live safe length tail =>
        exact .cons ⟨m, index, rfl, shifted, live, safe, length⟩ (ih _ tail)
  · intro related
    induction related with
    | nil => exact .nil _ _ _
    | @cons left right functions nextFunctions head tail ih =>
      obtain ⟨arity, body⟩ := left
      obtain ⟨nextArity, nextBody⟩ := right
      obtain ⟨m, index, same, shifted, live, safe, length⟩ := head
      simp only at same shifted live safe length
      subst nextArity
      exact .cons env nextEnv count arity m body nextBody index functions nextFunctions shifted live safe length ih

/-- A tracked environment slot maps to an in-range target slot carrying a
related value. -/
theorem envOk_getVar (m l : Nat) (index : Spt Nat) (env nextEnv : List Value) (n : Nat)
    (related : EnvOk m l index env nextEnv n) (tracked : n < l + m) :
    n < env.length ∧ getVar m l index n < nextEnv.length ∧
      ValueRel (@Flapjack.holEl Value ⟨unitValue⟩ n env)
        (@Flapjack.holEl Value ⟨unitValue⟩ (getVar m l index n) nextEnv) := by
  cases related with
  | outside _ _ _ _ _ _ beyond => omega
  | «local» _ _ _ _ _ _ below valueRel sourceBound targetBound =>
    simpa [getVar, below] using And.intro sourceBound (And.intro targetBound valueRel)
  | captured _ _ _ _ _ _ compact above below _ lookup sourceBound targetBound valueRel =>
    have notBelow : ¬ n < l := by omega
    simpa [getVar, notBelow, lookup] using And.intro sourceBound (And.intro targetBound valueRel)

/-- Successful environment selection preserves positions: each output slot
contains the value selected by the corresponding input index. -/
theorem lookupVars_position {α : Type} (indices : List Nat) (env values : List α)
    (position : Nat) (bound : position < indices.length) (run : lookupVars indices env = some values) :
    ∃ value, env[Flapjack.holEl position indices]? = some value ∧ values[position]? = some value := by
  induction indices generalizing position values with
  | nil => simp at bound
  | cons index rest ih =>
    cases selected : env[index]? with
    | none => simp [lookupVars, selected] at run
    | some value =>
      cases tailRun : lookupVars rest env with
      | none => simp [lookupVars, selected, tailRun] at run
      | some tail =>
        simp [lookupVars, selected, tailRun] at run
        subst values
        cases position with
        | zero => exact ⟨value, by simpa [Flapjack.holEl, Flapjack.holHd] using selected, by simp⟩
        | succ position =>
          have smaller : position < rest.length := by simpa using bound
          obtain ⟨result, source, target⟩ := ih tail position smaller tailRun
          exact ⟨result, by simpa [Flapjack.holEl_cons_succ] using source, by simpa using target⟩

/-- Restricting an environment to its distinct live slots preserves the
source relation at every live variable. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_ok_shifted_env"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem envOk_shiftedEnv (m l : Nat) (index : Spt Nat) (env nextEnv : List Value)
    (n : Nat) (live : List Nat) (selected : List Value)
    (h : EnvOk m l index env nextEnv n ∧ n ∈ live ∧ live.Nodup ∧
      lookupVars ((live.filter (· < m + l)).map (getVar m l index)) nextEnv = some selected) :
    EnvOk (m + l) 0 (shiftedEnv 0 (live.filter (· < m + l))) env selected n := by
  obtain ⟨related, member, distinct, run⟩ := h
  let _ : Nonempty Value := ⟨unitValue⟩
  by_cases tracked : n < m + l
  · let filtered := live.filter (· < m + l)
    have filteredMember : n ∈ filtered := by simp [filtered, member, tracked]
    have filteredDistinct : filtered.Nodup := distinct.filter _
    obtain ⟨position, bound, atPosition⟩ := List.mem_iff_getElem.mp filteredMember
    have nth : Flapjack.holEl position filtered = n := by
      rw [Flapjack.holEl_eq_getElem position filtered bound]
      exact atPosition
    have selectedIndex : Flapjack.holEl position (filtered.map (getVar m l index)) = getVar m l index n := by
      rw [Flapjack.holEl_eq_getElem position _ (by simpa using bound), List.getElem_map, atPosition]
    have mapLookup : sptLookup n (shiftedEnv 0 filtered) = some position := by
      have h := lookup_shiftedEnv_el filtered position 0 ⟨bound, filteredDistinct⟩
      simpa [nth] using h
    obtain ⟨value, sourceLookup, selectedLookup⟩ :=
      lookupVars_position (filtered.map (getVar m l index)) nextEnv selected position (by simpa using bound) run
    rw [selectedIndex] at sourceLookup
    have sourceInfo := List.getElem?_eq_some_iff.mp sourceLookup
    have selectedInfo := List.getElem?_eq_some_iff.mp selectedLookup
    have sourceValue : @Flapjack.holEl Value ⟨unitValue⟩ (getVar m l index n) nextEnv = value := by
      rw [Flapjack.holEl_eq_getElem _ _ sourceInfo.1]
      exact sourceInfo.2
    have selectedValue : @Flapjack.holEl Value ⟨unitValue⟩ position selected = value := by
      rw [Flapjack.holEl_eq_getElem _ _ selectedInfo.1]
      exact selectedInfo.2
    have sourceRelated := envOk_getVar m l index env nextEnv n related (by omega)
    apply EnvOk.captured (m + l) 0 (shiftedEnv 0 filtered) env selected n position (by omega) (by omega) (by omega)
    · simpa using mapLookup
    · exact sourceRelated.1
    · simpa using selectedInfo.1
    · simpa [sourceValue, selectedValue] using sourceRelated.2.2
  · exact .outside _ _ _ _ _ _ (by omega)

end Flapjack.Compiler.Backend.ClosAnnotate
