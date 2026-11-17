module

public import Flapjack.Compiler.Inference.Infer.TypeNameCheckSub

@[expose] public section

/-! Relating the two source type-name checking definitions. -/
namespace Flapjack.Compiler.Inference.Infer.TypeNameCheck
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.NamespaceHOL
  Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.InferTDisplay
  Flapjack.Translator.Monadic.MonadBase

private def formatCheck {σ α : Type} (f : MlString → MlString)
    (op : M σ α (Option Locs × Sum MlString MlString)) : M σ α (Option Locs × MlString) :=
  fun s => match op s with
    | (.success x, s') => (.success x, s')
    | (.failure (loc, .inl msg), s') => (.failure (loc, msg), s')
    | (.failure (loc, .inr name), s') => (.failure (loc, f name), s')

private theorem formatRet {σ α : Type} (f : MlString → MlString) (x : α) :
    formatCheck f (ret x : M σ α (Option Locs × Sum MlString MlString)) = ret x := by
  rfl

private theorem formatBind {σ α β : Type} (f : MlString → MlString)
    (op : M σ α (Option Locs × Sum MlString MlString))
    (next : α → M σ β (Option Locs × Sum MlString MlString)) :
    formatCheck f (bind op next) = bind (formatCheck f op) (fun x => formatCheck f (next x)) := by
  funext s
  cases h : op s with
  | mk result s' =>
    cases result with
    | success x => simp [formatCheck, Flapjack.Translator.Monadic.MonadBase.bind, h]
    | failure e =>
      rcases e with ⟨loc, err⟩
      cases err <;> simp [formatCheck, Flapjack.Translator.Monadic.MonadBase.bind, h]

mutual
private theorem checkEquiv {σ : Type} (t : AstT) (l : LocErrInfo) (f : MlString → MlString)
    (env : TenvAbbrev) (fvs : List MlString) :
    typeNameCheckSubst (state := σ) l f env fvs t = formatCheck f (typeNameCheckSub l env fvs t) := by
  cases t with
  | atvar tv =>
    funext s
    by_cases h : tv ∈ fvs <;>
      simp [typeNameCheckSubst, typeNameCheckSub, Operations.guard, Operations.failwith,
        ignoreBind, ret, formatCheck, h]
  | attup ts =>
    simp only [typeNameCheckSubst, typeNameCheckSub, formatBind, formatRet,
      ← checksEquiv ts l f env fvs]
  | atfun a b =>
    simp only [typeNameCheckSubst, typeNameCheckSub, formatBind, formatRet,
      ← checkEquiv a l f env fvs, ← checkEquiv b l f env fvs]
  | atapp ts tc =>
    simp only [typeNameCheckSubst, typeNameCheckSub, formatBind,
      ← checksEquiv ts l f env fvs]
    congr 1
    funext ts' s
    cases found : nsLookup env tc with
    | none =>
      simp [formatCheck, Flapjack.Translator.Monadic.MonadBase.bind, lookupStEx, found]
    | some entry =>
      rcases entry with ⟨tvs, body⟩
      by_cases h : tvs.length = ts.length <;>
        simp [formatCheck, Flapjack.Translator.Monadic.MonadBase.bind, lookupStEx, found,
          ignoreBind, Operations.guard, Operations.failwith, ret, h]
termination_by sizeOf t

private theorem checksEquiv {σ : Type} (ts : List AstT) (l : LocErrInfo) (f : MlString → MlString)
    (env : TenvAbbrev) (fvs : List MlString) :
    typeNameCheckSubstList (state := σ) l f env fvs ts = formatCheck f (typeNameCheckSubList l env fvs ts) := by
  cases ts with
  | nil => simp only [typeNameCheckSubstList, typeNameCheckSubList, formatRet]
  | cons t ts =>
    simp only [typeNameCheckSubstList, typeNameCheckSubList, formatBind, formatRet,
      ← checkEquiv t l f env fvs, ← checksEquiv ts l f env fvs]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferScript.sml" "to_type_name_check_sub"]
theorem toTypeNameCheckSub {σ : Type} :
    (∀ t l f env fvs,
      typeNameCheckSubst (state := σ) l f env fvs t = fun s =>
        match typeNameCheckSub l env fvs t s with
        | (.failure (loc, .inr name), s') => (.failure (loc, f name), s')
        | (.failure (loc, .inl msg), s') => (.failure (loc, msg), s')
        | (.success value, s') => (.success value, s')) ∧
    (∀ ts l f env fvs,
      typeNameCheckSubstList (state := σ) l f env fvs ts = fun s =>
        match typeNameCheckSubList l env fvs ts s with
        | (.failure (loc, .inr name), s') => (.failure (loc, f name), s')
        | (.failure (loc, .inl msg), s') => (.failure (loc, msg), s')
        | (.success values, s') => (.success values, s')) := by
  constructor
  · intro t l f env fvs
    rw [checkEquiv]
    funext s
    unfold formatCheck
    cases h : typeNameCheckSub l env fvs t s with
    | mk result next =>
      cases result with
      | success value => rfl
      | failure error => rcases error with ⟨loc, sum⟩; cases sum <;> rfl
  · intro ts l f env fvs
    rw [checksEquiv]
    funext s
    unfold formatCheck
    cases h : typeNameCheckSubList l env fvs ts s with
    | mk result next =>
      cases result with
      | success value => rfl
      | failure error => rcases error with ⟨loc, sum⟩; cases sum <;> rfl

end Flapjack.Compiler.Inference.Infer.TypeNameCheck
