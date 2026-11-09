module

public import Flapjack.Compiler.Backend.SourceToFlat.Helpers
public import Flapjack.NamespaceProps

@[expose] public section

/-! Binding source variable names and traces in the source-to-flat proof. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon

/-- Extending compiler environments preserves a predicate on variable bindings. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "nsAll_extend_env"]
theorem nsAll_extendEnv (P : Ident MlString MlString → VarName → Prop) (e1 e2 : Environment)
    (premises : nsAll P e1.v ∧ nsAll P e2.v) : nsAll P (extendEnv e1 e2).v := by
  have same : Classical.typeDecidableEq MlString = (inferInstance : DecidableEq MlString) :=
    Subsingleton.elim _ _
  have premises' : @nsAll MlString MlString VarName (Classical.typeDecidableEq MlString)
      (Classical.typeDecidableEq MlString) P e1.v ∧
      @nsAll MlString MlString VarName (Classical.typeDecidableEq MlString)
        (Classical.typeDecidableEq MlString) P e2.v := by
    rw [same]
    exact premises
  have result := nsAll_nsAppend P e1.v e2.v premises'
  change @nsAll MlString MlString VarName (Classical.typeDecidableEq MlString)
    (Classical.typeDecidableEq MlString) P (nsAppend e1.v e2.v) at result
  rw [same] at result
  simpa only [extendEnv] using result

/-- Bind each name to the local variable with its corresponding trace. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "bind_locals_def"]
def bindLocals {ModuleName : Type} (traces : List Tra) (locals : List MlString)
    (compMap : Namespace ModuleName MlString VarName) : Namespace ModuleName MlString VarName :=
  nsBindList (List.zipWith (fun trace name => (name, VarName.localName trace name)) traces locals) compMap

/-- A leading local binding is a leading trace and name in the binding fold. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "bind_locals_fold_nsBind"]
theorem bindLocals_fold_nsBind {ModuleName : Type} (nm : MlString) (t : Tra)
    (ts : List Tra) (locals : List MlString) (vMap : Namespace ModuleName MlString VarName) :
    nsBind nm (.localName t nm) (bindLocals ts locals vMap) =
      bindLocals (t :: ts) (nm :: locals) vMap := by
  rfl

private theorem zipLocals_append {α : Type} (funs : List (MlString × α)) (trace : Tra)
    (traces : List Tra) (locals : List MlString) :
    List.zipWith (fun t x => (x, VarName.localName t x))
        (List.replicate funs.length trace ++ traces) (funs.map Prod.fst ++ locals) =
      (funs.map Prod.fst).map (fun name => (name, VarName.localName trace name)) ++
        List.zipWith (fun t x => (x, VarName.localName t x)) traces locals := by
  induction funs with
  | nil => rfl
  | cons pair rest ih =>
    cases pair
    simp [List.replicate_succ, ih, List.map_map]

/-- Appending a namespace of uniformly traced function names is equivalent to
adding those names and traces to the front of the local bindings. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "nsAppend_bind_locals"]
theorem nsAppend_bindLocals {ModuleName α : Type} (funs : List (MlString × α))
    (trace : Tra) (traces : List Tra) (locals : List MlString)
    (compMap : Namespace ModuleName MlString VarName) :
    nsAppend (alistToNs ((funs.map Prod.fst).map (fun name => (name, VarName.localName trace name))))
        (bindLocals traces locals compMap) =
      bindLocals (List.replicate funs.length trace ++ traces) (funs.map Prod.fst ++ locals) compMap := by
  simp only [bindLocals, ← nsAppend_to_nsBindList, zipLocals_append]
  cases compMap
  simp [nsAppend, alistToNs, List.append_assoc]

/-- Pattern bindings correspond to a list of local traces of the same length. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "nsBindList_pat_tups_bind_locals"]
theorem nsBindList_patTups_bindLocals {ModuleName : Type} (names : List MlString)
    (trace : Tra) (traces : List Tra) (locals : List MlString)
    (compMap : Namespace ModuleName MlString VarName) :
    ∃ patternTraces,
      nsBindList (patTups trace names) (bindLocals traces locals compMap) =
        bindLocals (patternTraces ++ traces) (names ++ locals) compMap ∧
      patternTraces.length = names.length := by
  induction names with
  | nil => exact ⟨[], by simp [patTups, nsBindList], rfl⟩
  | cons name rest ih =>
    obtain ⟨patternTraces, h, hlen⟩ := ih
    refine ⟨mkCons trace (rest.length + 1) :: patternTraces, ?_, by simp [hlen]⟩
    simp [patTups, nsBindList, bindLocals] at h ⊢
    exact congrArg (nsBind name (VarName.localName (mkCons trace (rest.length + 1)) name)) h

end Flapjack.Compiler.Backend.SourceToFlat
