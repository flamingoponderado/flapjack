module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationFn
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxLetrec

@[expose] public section


/-! Infrastructure for the recursive-closure case of optimizer simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Letrec
open ClosSem ClosProps ClosProps.StateGlobalSafety Relations KnownUnchanged BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Optimizing a list of function bodies that cannot write globals gives
related functions in any approximation tree extending the initial tree.
This is Flapjack proof infrastructure for the recursive-closure case. -/
theorem optimizedFunctionsRelated (c : Config) (fns : List (Nat × ClosLang.Exp))
    (clos aenv : List ValApprox) (g0 g : Spt ValApprox)
    (empty : funGlobals fns = FlatProps.emptyGlobalBag)
    (safeClos : ∀ a ∈ clos, valApproxSgcFree a)
    (safeEnv : ∀ a ∈ aenv, valApproxSgcFree a)
    (safeGlobals : globalsApproxSgcFree g0) (sub : sptSubspt g0 g) :
    List.Forall₂ (fRel c (clos ++ aenv) g) fns
      (fns.map (fun (n, e) =>
        (n, (knownSourceHead (knownListTotal c [e]
          (List.replicate n .other ++ clos ++ aenv) g0).1).1))) := by
  have bodiesEmpty : ∀ f ∈ fns, setGlobals f.2 = FlatProps.emptyGlobalBag := by
    have h := (elistGlobalsEmpty (fns.map Prod.snd)).1 (by simpa [funGlobals_eq_elist] using empty)
    intro f member
    exact h f.2 (List.mem_map.mpr ⟨f, member, rfl⟩)
  have each : ∀ f ∈ fns, fRel c (clos ++ aenv) g f
      (match f with | (n, e) => (n, (knownSourceHead (knownListTotal c [e]
        (List.replicate n .other ++ clos ++ aenv) g0).1).1)) := by
   intro f member
   rcases f with ⟨arity, body⟩
   have safe : ∀ a ∈ List.replicate arity ValApprox.other ++ clos ++ aenv, valApproxSgcFree a := by
    intro a mem
    simp only [List.mem_append] at mem
    rcases mem with (mem | mem) | mem
    · have eq := (List.mem_replicate.mp mem).2
      subst a
      simp [valApproxSgcFree]
    · exact safeClos a mem
    · exact safeEnv a mem
   cases hk : knownListTotal c [body] (List.replicate arity .other ++ clos ++ aenv) g0 with
   | mk eas after =>
    obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body
      (List.replicate arity .other ++ clos ++ aenv) g0 after eas hk
    subst eas
    have noWrites : elistGlobals [body] = FlatProps.emptyGlobalBag := by
      apply (elistGlobalsEmpty [body]).2
      intro e he
      simp only [List.mem_singleton] at he
      subst e
      exact bodiesEmpty (arity, body) member
    have unchanged := knownUnchangedGlobals c [body]
      (List.replicate arity .other ++ clos ++ aenv) g0 [(be, ba)] after ⟨hk, noWrites⟩
    subst after
    simp only [hk, knownSourceHead]
    refine ⟨rfl, g0, g0, ba, c.inlineFactor, sub, ?_, safeGlobals, ?_⟩
    · simpa [List.append_assoc] using safe
    · simpa [List.append_assoc] using hk
  clear empty bodiesEmpty
  induction fns with
  | nil => exact .nil
  | cons f fs ih =>
    apply List.Forall₂.cons (each f (by simp))
    apply ih
    intro f member; exact each f (by simp [member])

/-- Building closures at the same indices preserves the value relation when
their captured environments and function bodies are related. This is Flapjack
proof infrastructure for the recursive-closure case. -/
theorem recursiveClosuresRelated (c : Config) (g : Spt ValApprox) (loc : Option Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (env1 extra1 env2 extra2 : List ClosSem.Value)
    (aenv : List ValApprox)
    (fnSyntax : ∀ f ∈ fns1, everyFnVarsNone [f.2])
    (free : ∀ f ∈ fns1, fvMax (f.1 + fns1.length + env1.length) [f.2])
    (envRel : List.Forall₂ (ValueRel c g) env1 env2)
    (approx : List.Forall₂ ValApproxVal aenv env1)
    (functions : List.Forall₂ (fRel c ((match loc with
      | none => List.replicate fns1.length .other
      | some n => closGenNoInline n 0 fns1) ++ aenv) g) fns1 fns2)
    (indices : List Nat) :
    List.Forall₂ (ValueRel c g)
      (indices.map (fun i => .recclosure loc [] (env1 ++ extra1) fns1 i))
      (indices.map (fun i => .recclosure loc [] (env2 ++ extra2) fns2 i)) := by
  induction indices with
  | nil => exact .nil
  | cons i rest ih =>
    exact .cons (.recclosure loc [] [] env1 extra1 env2 extra2 fns1 fns2 i aenv
      fnSyntax free .nil envRel approx functions) ih

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Letrec
