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

/-- A non-shadowed source binding in the global environment invariant is
fetched by its compiled global lookup. This is Flapjack infrastructure over
the factored relations and the partial flat-operation dispatcher. -/
theorem globalEnvInv_doApp {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (shadowers : VarN → Prop)
    (id : Ident ModN VarN) (source : SemanticPrimitivesHOL.Value) (state : FlatSem.State C F)
    (globalsEq : state.globals = genv.v) (inv : GlobalEnvInv genv compMap shadowers sourceEnv)
    (unshadowed : ¬(∃ name, shadowers name ∧ id = .short name))
    (lookup : nsLookup sourceEnv.v id = some source) :
    ∃ n flat trace, nsLookup compMap.v id = some (.glob trace n) ∧ ValueRel genv source flat ∧
      FlatSem.doAppFlat state (.globalVarLookup n) [] = some (some (state, .val flat)) := by
  cases inv with
  | intro _ _ _ values constructors =>
    exact globalLookupRel_doApp genv compMap id source state globalsEq (values id source unshadowed lookup)

end Flapjack.Compiler.Backend.SourceToFlat
