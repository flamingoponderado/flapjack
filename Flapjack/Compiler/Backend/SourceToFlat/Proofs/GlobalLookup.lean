import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRel
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyFlat

/-! Global-variable lookup infrastructure over the factored source-to-flat
relations. The full evaluator and HOL correspondence remain open. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- A related global source binding is fetched by the corresponding flat
global-lookup operation. This is Flapjack infrastructure over the factored
value relation and the partial flat-operation dispatcher. -/
theorem globalLookupRel_doApp {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (id : Ident ModN VarN) (source : SemanticPrimitivesHOL.Value) (state : FlatSem.State C F)
    (globalsEq : state.globals = genv.v) (related : GlobalLookupRel genv compMap id source) :
    ∃ n flat trace, nsLookup compMap.v id = some (.glob trace n) ∧ ValueRel genv source flat ∧
      FlatSem.doAppFlat state (.globalVarLookup n) [] = some (some (state, .val flat)) := by
  cases related with
  | intro _ _ _ n flat trace lookup bound slot valueRel =>
    have slotLookup : genv.v[n]? = some (some flat) := by
      cases h : genv.v[n]? with
      | none => simp [h] at slot
      | some entry =>
        cases entry with
        | none => simp [h] at slot
        | some value =>
          simp [h] at slot
          subst value
          rfl
    refine ⟨n, flat, trace, lookup, valueRel, ?_⟩
    simp [FlatSem.doAppFlat, globalsEq, slotLookup]

end Flapjack.Compiler.Backend.SourceToFlat
