import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGlobalSafety
import Flapjack.Compiler.Backend.Semantics.ClosProps.GlobalSafety
import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
import Flapjack.Compiler.Backend.Semantics.ClosSem.Thunk
import Aesop

/-! Global-write safety at closure application. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem ClosProps
open FlatProps (emptyGlobalBag)

/-- Fully applying a safe closure to safe arguments produces a safe body,
environment, and remaining arguments. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "dest_closure_Full_sgc_free"]
theorem destClosureFullSgcFree (maxApp : Nat) (location : Option Nat) (f arg0 : ClosSem.Value)
    (args : List ClosSem.Value) (body : ClosLang.Exp) (env rest : List ClosSem.Value)
    (h : destClosure maxApp location f (arg0 :: args) = some (.fullApp body env rest) ∧
      vsgcFree f ∧ vsgcFree arg0 ∧ (∀ v ∈ args, vsgcFree v)) :
    setGlobals body = emptyGlobalBag ∧ (∀ v ∈ env, vsgcFree v) ∧
      (∀ v ∈ rest, vsgcFree v) := by
  rcases h with ⟨found, fnSafe, firstSafe, argsSafe⟩
  cases f <;> simp only [destClosure] at found <;> try contradiction
  all_goals simp only [vsgcFree] at fnSafe
  all_goals repeat' split at found
  all_goals simp_all only [Option.some.injEq, AppKind.fullApp.injEq, reduceCtorEq]
  all_goals rcases found with ⟨_, rfl, rfl⟩
  all_goals try (have allBodies := (elistGlobalsEmpty _).1 fnSafe.1)
  all_goals aesop (add simp [vsgcFree, List.mem_append, List.mem_reverse, List.mem_cons, List.mem_map]) (add safe forward [List.mem_of_mem_take, List.mem_of_mem_drop, List.mem_of_getElem?])


/-- Updating a reference with a safe thunk preserves state safety. This is a
Lean helper without a separate HOL declaration. -/
private theorem updateSafeThunk {C F : Type} (s : State C F) (index : Nat)
    (mode : Flapjack.AstHOL.ThunkMode) (value : ClosSem.Value)
    (safe : ClosProps.StateGlobalSafety.ssgcFree s) (valueSafe : vsgcFree value) :
    ClosProps.StateGlobalSafety.ssgcFree {s with refs := s.refs.updateEq (index, .thunk mode value)} := by
  rcases safe with ⟨code, arrays, thunks, globals, oracle⟩
  refine ⟨code, ?_, ?_, globals, oracle⟩
  · intro key values found
    by_cases same : key = index
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] at found
    · apply arrays key values
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using found
  · intro key mode' value' found
    by_cases same : key = index
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] at found
      rcases found with ⟨_, rfl⟩
      exact valueSafe
    · apply thunks key mode' value'
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using found

/-- The closure state roundtrips through its canonical finite-map view. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Successful singleton thunk updates preserve closure-state safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "update_thunk_ssgc_free"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, refs])]
theorem updateThunkSsgcFree {C F : Type} (s : ClosSem.State C F) (flag : Bool) (ptr : Nat)
    (values : List ClosSem.Value) (refs : HolFiniteMapExact Nat (Ref ClosSem.Value))
    (h : ClosProps.StateGlobalSafety.ssgcFree s ∧ (∀ v ∈ values, vsgcFree v) ∧
      updateThunk [.refPtr flag ptr] s.refs values = some refs) :
    ClosProps.StateGlobalSafety.ssgcFree {s with refs := refs} := by
  rcases h with ⟨safe, valuesSafe, run⟩
  unfold updateThunk at run
  repeat' split at run
  all_goals simp_all [destThunk, storeThunk]
  split at run <;> simp_all
  subst refs
  exact updateSafeThunk _ _ _ _ safe valuesSafe

end Flapjack.Compiler.Backend.ClosKnown
