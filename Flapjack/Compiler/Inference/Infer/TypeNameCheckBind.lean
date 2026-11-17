module

public import Flapjack.Compiler.Inference.Infer.TypeNameCheckEquiv

@[expose] public section

/-! Binding laws for source type-name checks. -/
namespace Flapjack.Compiler.Inference.Infer.TypeNameCheck
open Flapjack.AstHOL Flapjack.TypeSystemHOL
  Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Translator.Monadic.MonadBase

@[hol "cakeml/compiler/inference/inferScript.sml" "bind_type_name_check_subst"]
theorem bindTypeNameCheckSubst {σ α β : Type} (l : LocErrInfo) (f : MlString → MlString)
    (env : TenvAbbrev) (fvs : List MlString) (t : AstT) (ts : List AstT)
    (g : SemanticT → M σ α (Option Locs × MlString))
    (gs : List SemanticT → M σ β (Option Locs × MlString)) :
    (bind (typeNameCheckSubst l f env fvs t) g = fun s =>
      match typeNameCheckSub l env fvs t s with
      | (.failure (loc, .inr name), s') => (.failure (loc, f name), s')
      | (.failure (loc, .inl msg), s') => (.failure (loc, msg), s')
      | (.success value, s') => g value s') ∧
    (bind (typeNameCheckSubstList l f env fvs ts) gs = fun s =>
      match typeNameCheckSubList l env fvs ts s with
      | (.failure (loc, .inr name), s') => (.failure (loc, f name), s')
      | (.failure (loc, .inl msg), s') => (.failure (loc, msg), s')
      | (.success values, s') => gs values s') := by
  constructor
  · rw [(toTypeNameCheckSub (σ := σ)).1 t l f env fvs]
    funext s
    cases h : typeNameCheckSub l env fvs t s with
    | mk result next =>
      cases result with
      | success value => simp [Flapjack.Translator.Monadic.MonadBase.bind, h]
      | failure error =>
        rcases error with ⟨loc, sum⟩
        cases sum <;> simp [Flapjack.Translator.Monadic.MonadBase.bind, h]
  · rw [(toTypeNameCheckSub (σ := σ)).2 ts l f env fvs]
    funext s
    cases h : typeNameCheckSubList l env fvs ts s with
    | mk result next =>
      cases result with
      | success value => simp [Flapjack.Translator.Monadic.MonadBase.bind, h]
      | failure error =>
        rcases error with ⟨loc, sum⟩
        cases sum <;> simp [Flapjack.Translator.Monadic.MonadBase.bind, h]

@[hol "cakeml/compiler/inference/inferScript.sml" "ignore_bind_type_name_check_subst"]
theorem ignoreBindTypeNameCheckSubst {σ α β : Type} (l : LocErrInfo) (f : MlString → MlString)
    (env : TenvAbbrev) (fvs : List MlString) (t : AstT) (ts : List AstT)
    (g : M σ α (Option Locs × MlString))
    (gs : M σ β (Option Locs × MlString)) :
    (ignoreBind (typeNameCheckSubst l f env fvs t) g = fun s =>
      match typeNameCheckSub l env fvs t s with
      | (.failure (loc, .inr name), s') => (.failure (loc, f name), s')
      | (.failure (loc, .inl msg), s') => (.failure (loc, msg), s')
      | (.success _, s') => g s') ∧
    (ignoreBind (typeNameCheckSubstList l f env fvs ts) gs = fun s =>
      match typeNameCheckSubList l env fvs ts s with
      | (.failure (loc, .inr name), s') => (.failure (loc, f name), s')
      | (.failure (loc, .inl msg), s') => (.failure (loc, msg), s')
      | (.success _, s') => gs s') := by
  constructor
  · rw [(toTypeNameCheckSub (σ := σ)).1 t l f env fvs]
    funext s
    cases h : typeNameCheckSub l env fvs t s with
    | mk result next =>
      cases result with
      | success value => simp [ignoreBind, h]
      | failure error =>
        rcases error with ⟨loc, sum⟩
        cases sum <;> simp [ignoreBind, h]
  · rw [(toTypeNameCheckSub (σ := σ)).2 ts l f env fvs]
    funext s
    cases h : typeNameCheckSubList l env fvs ts s with
    | mk result next =>
      cases result with
      | success value => simp [ignoreBind, h]
      | failure error =>
        rcases error with ⟨loc, sum⟩
        cases sum <;> simp [ignoreBind, h]

end Flapjack.Compiler.Inference.Infer.TypeNameCheck
