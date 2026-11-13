module

public import Flapjack.Compiler.Backend.ClosCall.Stubs
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars.Append

@[expose] public section

/-! Source invariants for the direct-call stub generators. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- The recursive stub generator is the indexed map in the source theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_list_MAPi"]
theorem callsListSource_mapIdx {A B : Type} (t : BackendCommon.Tra) :
    ∀ (loc : Nat) (_tra : A) (n : Nat),
      (callsListSource (A := B) t n loc) =
        fun fns => fns.mapIdx (fun i p =>
          (p.1, .call t 0 (loc + 2 * i + 1) (variablesSource t 1 p.1))) := by
  intro loc tra n
  funext fns
  induction fns generalizing loc n with
  | nil => simp [callsListSource]
  | cons fn rest ih =>
    rcases fn with ⟨arity, payload⟩
    simp only [callsListSource, List.mapIdx_cons]
    congr 1
    convert ih (loc + 2) (n + 1) using 1
    congr 1
    funext i p
    congr 2
    omega

/-- Generated variables have exactly the indices below the requested count. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "fv_GENLIST_Var_tra"]
theorem freeVars_variables (v : Nat) : ∀ (count : Nat) (trace : BackendCommon.Tra) (index : Nat),
    freeVars v (variablesSource trace index count) ↔ v < count := by
  intro count
  induction count with
  | zero => intro trace index; simp [variablesSource, freeVars]
  | succ count ih =>
    intro trace index
    simp [variablesSource, freeVars_append, freeVars, freeVarExp, ih]
    omega

/-- Generated variables use exactly the indices below the list length. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "fv_GENLIST_Var_alt"]
theorem freeVars_variables_alt (v : Nat) (count index : Nat) (trace : BackendCommon.Tra) :
    freeVars v (variablesSource trace index count) ↔ v < count :=
  freeVars_variables v count trace index

/-- Generated variables contain no label operations. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "no_Labels_GENLIST_Var"]
theorem noLabels_variables : ∀ (trace : BackendCommon.Tra) (index count : Nat),
    ∀ expression ∈ variablesSource trace index count, noLabels expression := by
  intro trace index count
  induction count generalizing index with
  | zero => simp [variablesSource]
  | succ count ih =>
    intro expression member
    simp only [variablesSource, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ih (index + 1) expression member
    · simp [noLabels]

/-- Every generated direct-call stub contains no label operation. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "no_Labels_calls_list"]
theorem noLabels_callsList {α : Type} : ∀ (trace : BackendCommon.Tra) (index loc : Nat)
    (functions : List (Nat × α)),
    ∀ expression ∈ (callsListSource trace index loc functions).map Prod.snd, noLabels expression := by
  intro trace index loc functions
  induction functions generalizing index loc with
  | nil => simp [callsListSource]
  | cons entry rest ih =>
    obtain ⟨arity, body⟩ := entry
    intro expression member
    simp only [callsListSource, List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · simpa [noLabels] using (noLabelsList_iff _).mpr (noLabels_variables trace 1 arity)
    · exact ih (index + 1) (loc + 2) expression member

/-- Generated variables obey any application-arity limit. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "obeys_max_app_GENLIST_Var"]
theorem obeysMaxApp_variables (limit : Nat) : ∀ (trace : BackendCommon.Tra) (index count : Nat),
    ∀ expression ∈ variablesSource trace index count, obeysMaxApp limit expression := by
  intro trace index count
  induction count generalizing index with
  | zero => simp [variablesSource]
  | succ count ih =>
    intro expression member
    simp only [variablesSource, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ih (index + 1) expression member
    · simp [obeysMaxApp]

/-- Every generated direct-call stub obeys any application-arity limit. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "obeys_max_app_calls_list"]
theorem obeysMaxApp_callsList {α : Type} (limit : Nat) :
    ∀ (trace : BackendCommon.Tra) (index loc : Nat) (functions : List (Nat × α)),
      ∀ expression ∈ (callsListSource trace index loc functions).map Prod.snd,
        obeysMaxApp limit expression := by
  intro trace index loc functions
  induction functions generalizing index loc with
  | nil => simp [callsListSource]
  | cons entry rest ih =>
    obtain ⟨arity, body⟩ := entry
    intro expression member
    simp only [callsListSource, List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · simpa [obeysMaxApp] using (obeysMaxAppList_iff _ _).mpr (obeysMaxApp_variables limit trace 1 arity)
    · exact ih (index + 1) (loc + 2) expression member

end Flapjack.Compiler.Backend.ClosCall
