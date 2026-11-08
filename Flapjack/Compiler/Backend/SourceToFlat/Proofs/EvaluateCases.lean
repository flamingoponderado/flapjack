import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalLookup
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
import Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Flapjack.EvaluateHOL.Definition
import Flapjack.Misc.ListEl

/-! Source-to-flat lookup and variable helpers, including the HOL
`env_rel_lookup` port. The untagged helpers are Flapjack-specific infrastructure
over the factored relations and the clocked flat evaluator. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

namespace EnvRelLookupReview

/-- The global environment uses the reviewed finite-map representation. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

end EnvRelLookupReview

/-- Pointwise relation at an index bounded by the second list. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "LIST_REL_IMP_EL2"]
theorem listRel_imp_el2 {α β : Type} [Nonempty α] [Nonempty β]
    (relation : α → β → Prop) (xs : List α) (ys : List β)
    (related : List.Forall₂ relation xs ys) (i : Nat) (bound : i < ys.length) :
    relation (Flapjack.holEl i xs) (Flapjack.holEl i ys) := by
  have leftBound : i < xs.length := by simpa [related.length_eq] using bound
  rw [Flapjack.holEl_eq_getElem i xs leftBound, Flapjack.holEl_eq_getElem i ys bound]
  exact related.get leftBound bound

/-- Pointwise relation at an index bounded by the first list. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "LIST_REL_IMP_EL"]
theorem listRel_imp_el {α β : Type} [Nonempty α] [Nonempty β]
    (relation : α → β → Prop) (xs : List α) (ys : List β)
    (related : List.Forall₂ relation xs ys) (i : Nat) (bound : i < xs.length) :
    relation (Flapjack.holEl i xs) (Flapjack.holEl i ys) := by
  have rightBound : i < ys.length := by simpa [← related.length_eq] using bound
  exact listRel_imp_el2 relation xs ys related i rightBound

/-- A list is nonempty exactly when it has a head and tail. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "NOT_NULL_EQ"]
theorem notNull_eq_cons {α : Type} (xs : List α) :
    xs ≠ [] ↔ ∃ head tail, xs = head :: tail := by
  cases xs <;> simp

/-- Evaluating a Boolean expression yields its flat Boolean value. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "evaluate_Bool"
  (fmap_as_finite_support := [c, tys])]
theorem evaluate_bool {C F : Type} (genv : GlobalEnv) (source : State F)
    (flat : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value) (t : Tra) (b : Bool)
    (_premises : StateRel genv source flat ∧ genvCOk genv.c) :
    FlatSem.evaluate env flat [FlatLang.mkBool t b] = (flat, .val [FlatSem.boolValue b]) := by
  cases b <;> simp [FlatSem.evaluate, FlatLang.mkBool, FlatSem.boolValue]

/-- Flat Boolean values distinguish their Boolean arguments. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "Boolv_11"]
theorem boolValue_eq_iff (b b' : Bool) : FlatSem.boolValue b = FlatSem.boolValue b' ↔ b = b' := by
  cases b <;> cases b' <;> simp [FlatSem.boolValue, boolToTag, trueTag, falseTag]

/-- An option case yielding a proposition separates into its two constructors. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "opt_case_bool_eq"]
theorem optionCase_bool_eq {α : Type} (opt : Option α) (nc : Prop) (scc : α → Prop) :
    (match opt with | none => nc | some x => scc x) ↔
      (opt = none ∧ nc) ∨ ∃ x, opt = some x ∧ scc x := by
  cases opt <;> simp

/-- A local lookup in related environments produces a related flat value. -/
theorem envRel_lookup (genv : GlobalEnv) (source : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flat : List (VarN × FlatSem.Value)) (related : EnvRel genv source flat)
    (name : VarN) (value : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup source (.short name) = some value) :
    ∃ flatValue, flat.lookup name = some flatValue ∧ ValueRel genv value flatValue := by
  cases related with
  | empty => simp [nsEmpty, nsLookup] at lookup
  | bind key sourceValue sourceEnv flatEnv flatValue envRel valueRel =>
    cases sourceEnv with
    | bind sourceValues sourceModules =>
      by_cases same : key = name
      · subst name
        simp [nsBind, nsLookup] at lookup
        subst value
        exact ⟨flatValue, by simp, valueRel⟩
      · have neq : (name == key) = false := by
          change decide (name = key) = false
          simp [Ne.symm same]
        simp [nsBind, nsLookup, List.lookup_cons, neq] at lookup
        obtain ⟨found, hfound, hrel⟩ := envRel_lookup genv _ flatEnv envRel name value lookup
        exact ⟨found, by simpa [List.lookup_cons, neq] using hfound, hrel⟩
termination_by flat.length

/-- An association-list lookup is preserved by related local environments. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_rel_lookup"
  (fmap_as_finite_support := [c, tys])]
theorem envRel_alist_lookup (genv : GlobalEnv) (source : List (VarN × SemanticPrimitivesHOL.Value))
    (name : VarN) (value : SemanticPrimitivesHOL.Value) (flat : List (VarN × FlatSem.Value))
    (premises : source.lookup name = some value ∧ EnvRel genv (alistToNs source) flat) :
    ∃ flatValue, ValueRel genv value flatValue ∧ flat.lookup name = some flatValue := by
  obtain ⟨lookup, related⟩ := premises
  have sourceLookup : nsLookup (alistToNs source : Namespace ModN VarN SemanticPrimitivesHOL.Value)
      (.short name) = some value := by simpa [alistToNs, nsLookup] using lookup
  obtain ⟨flatValue, flatLookup, valueRel⟩ := envRel_lookup genv (alistToNs source) flat related name value sourceLookup
  exact ⟨flatValue, valueRel, flatLookup⟩

/-- Global-variable simulation using both clocked evaluators without extra fuel. -/
theorem evaluate_global_unbounded {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (globalsEq : flatState.globals = genv.v)
    (trace : List VarN) (id : Ident ModN VarN) (source : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup sourceEnv.v id = some source) (related : GlobalLookupRel genv compMap id source) :
    ∃ flat, EvaluateHOL.evaluate sourceState sourceEnv [.var id] = (sourceState, .val [source]) ∧
      FlatSem.evaluate flatEnv flatState [compileExp trace compMap (.var id)] =
        (flatState, .val [flat]) ∧ ValueRel genv source flat ∧ StateRel genv sourceState flatState := by
  obtain ⟨n, flat, t, compiled, valueRel, flatDo⟩ :=
    globalLookupRel_doApp genv compMap id source flatState globalsEq related
  refine ⟨flat, ?_, ?_, valueRel, statesRel⟩
  · simp [EvaluateHOL.evaluate, lookup]
  · simp [compileExp, compiled, compileVar, FlatSem.evaluate, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp, flatDo]
end Flapjack.Compiler.Backend.SourceToFlat
