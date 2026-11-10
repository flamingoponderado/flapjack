module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApprox
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownUnchanged

@[expose] public section


/-! Closure-creation case of known-function approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Fn
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Closure creation returns a value described by the optimizer's original
body approximation. This is Flapjack proof infrastructure. -/
private theorem fnResultApprox {C F : Type} (c : Config) (name : Basis.Pure.MlString.MlString)
    (loc : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : State C F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State C F) (run : evaluate [.fn name loc selected arity body] env s0 = (res, s)) :
    ∀ vs, res = .val vs → List.Forall₂ ValApproxVal
      [match loc with | none => .other | some n => closApproxHOL c.inlineMaxBodySize n arity body] vs := by
  rw [evaluate.eq_def] at run
  dsimp only at run
  split at run
  · cases loc with
    | none =>
      cases selected with
      | none =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        intro vs h; cases h
        exact .cons (.other _) .nil
      | some selected =>
        cases found : lookupVars selected env with
        | none => simp [found] at run; rcases run with ⟨rfl, rfl⟩; intro vs h; cases h
        | some captured =>
          simp [found] at run
          rcases run with ⟨rfl, rfl⟩
          intro vs h; cases h
          exact .cons (.other _) .nil
    | some loc =>
      cases selected with
      | none =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        intro vs h; cases h
        simp only
        unfold closApproxHOL
        split
        · exact .cons (.closNoInline ..) .nil
        · exact .cons (.clos ..) .nil
      | some selected =>
        cases found : lookupVars selected env with
        | none => simp [found] at run; rcases run with ⟨rfl, rfl⟩; intro vs h; cases h
        | some captured =>
          simp [found] at run
          rcases run with ⟨rfl, rfl⟩
          intro vs h; cases h
          simp only
          unfold closApproxHOL
          split
          · exact .cons (.closNoInline ..) .nil
          · exact .cons (.clos ..) .nil
  · simp at run
    rcases run with ⟨rfl, rfl⟩
    intro vs h; cases h

/-- Closure-creation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxFn {C F : Type} (c : Config) (name : Basis.Pure.MlString.MlString)
    (loc : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox)
    (_bodyIH : KnownApproxInvariant C F c [body] (List.replicate arity .other ++ aenv) g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.fn name loc selected arity body] aenv g0 = (eas, g) ∧
      evaluate [.fn name loc selected arity body] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.fn name loc selected arity body] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.fn name loc selected arity body] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.fn name loc selected arity body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, _, _, approx, _, _, _, _, safe, _, _⟩
  have bodyEmpty : setGlobals body = FlatProps.emptyGlobalBag := by
    have h := safe (.fn name loc selected arity body) (by simp)
    simpa [esgcFree] using h
  have emptyBody : elistGlobals [body] = FlatProps.emptyGlobalBag := by
    funext i
    simp [elistGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, bodyEmpty, Flapjack.bagUnion, Flapjack.emptyBag]
  cases hk : knownListTotal c [body] (List.replicate arity .other ++ aenv) g0 with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ :=
      knownListTotal_single_result c body (List.replicate arity .other ++ aenv) g0 bodyG bodyEas hk
    subst bodyEas
    have unchanged := KnownUnchanged.knownUnchangedGlobals c [body]
      (List.replicate arity .other ++ aenv) g0 [(bodyExpr, bodyApprox)] bodyG ⟨hk, emptyBody⟩
    have preserved : stateGlobalsApprox s0 bodyG := by simpa [← unchanged] using approx
    have resultApprox := fnResultApprox c name loc selected arity body (env ++ extra) s0 res s run
    have sameState : s = s0 := by
      rw [evaluate.eq_def] at run
      dsimp only at run
      repeat' split at run <;> simp_all
    subst s
    rw [knownListTotal_fn, hk] at known
    simp [knownSourceHead] at known
    rcases known with ⟨rfl, rfl⟩
    refine ⟨preserved, ?_⟩
    cases loc <;> simpa using resultApprox

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Fn
