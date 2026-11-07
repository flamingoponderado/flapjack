import Flapjack.SemanticPrimitivesHOL.Operations
import Mathlib.Data.List.Basic
/-! Characterization of source closure application. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.NamespaceHOL
/-- Successful application selects either a closure or a well-formed recursive closure. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "do_opapp_cases"]
theorem doOpApp_cases (env' : SemEnv Value) (vs : List Value) (v : Flapjack.AstHOL.Exp) :
    doOpApp vs = some (env', v) ↔
      (∃ v₂ env'' n e, vs = [.closure env'' n e, v₂] ∧
        env' = { env'' with v := nsBind n v₂ env''.v } ∧ v = e) ∨
      (∃ v₂ env'' funs n' n'' e, vs = [.recclosure env'' funs n', v₂] ∧
        findRecFun n' funs = some (n'', e) ∧ (funs.map fun (f, _, _) => f).Nodup ∧
        env' = { env'' with v := nsBind n'' v₂ (buildRecEnv funs env'' env''.v) } ∧ v = e) := by
  cases vs with
  | nil => simp [doOpApp]
  | cons f rest =>
    cases rest with
    | nil => simp [doOpApp]
    | cons arg rest =>
      cases rest with
      | cons _ _ => simp [doOpApp]
      | nil =>
        cases f with
        | recclosure env funs name =>
          cases h : findRecFun name funs with
          | none => simp [doOpApp, h]
          | some result =>
            rcases result with ⟨param, body⟩
            simp [doOpApp, h, and_comm, and_assoc, eq_comm]
        | _ => simp [doOpApp, and_comm, eq_comm]
end Flapjack.SemanticPrimitivesProps
