import Flapjack.Compiler.Backend.SourceToFlat.Config

/-! Binding source variable names and traces in the source-to-flat proof. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon

/-- Bind each name to the local variable with its corresponding trace. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "bind_locals_def"]
def bindLocals {ModuleName : Type} (traces : List Tra) (locals : List MlString)
    (compMap : Namespace ModuleName MlString VarName) : Namespace ModuleName MlString VarName :=
  nsBindList (List.zipWith (fun trace name => (name, VarName.localName trace name)) traces locals) compMap

private theorem bindList_eq_append {M N V : Type} (bindings : List (N × V))
    (env : Namespace M N V) : nsBindList bindings env = nsAppend (alistToNs bindings) env := by
  cases env with
  | bind values modules =>
    induction bindings with
    | nil => rfl
    | cons p rest ih =>
      simp only [nsBindList, List.foldr_cons] at ih ⊢
      rw [ih]
      cases p
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
  simp only [bindLocals, bindList_eq_append, zipLocals_append]
  cases compMap
  simp [nsAppend, alistToNs, List.append_assoc]

end Flapjack.Compiler.Backend.SourceToFlat
