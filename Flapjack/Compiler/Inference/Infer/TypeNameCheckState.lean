module

public import Flapjack.Compiler.Inference.Infer.TypeNameCheck

@[expose] public section

/-! State preservation needed to relate source checking to executable inference. -/
namespace Flapjack.Compiler.Inference.Infer.TypeNameCheck
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.Misc.Location
  Flapjack.Basis.Pure.MlString Flapjack.Translator.Monadic.MonadBase
  Flapjack.Compiler.Inference.Infer.Operations

private def Preserves {σ α ε : Type} (op : M σ α ε) : Prop :=
  ∀ s, (op s).2 = s

private theorem preservesRet {σ α ε : Type} (x : α) : Preserves (ret x : M σ α ε) := by
  intro s
  rfl

private theorem preservesBind {σ α β ε : Type} (op : M σ α ε) (next : α → M σ β ε)
    (h : Preserves op) (hn : ∀ a, Preserves (next a)) : Preserves (bind op next) := by
  intro s
  have hs := h s
  cases eq : op s with
  | mk result state =>
    simp only [eq] at hs
    subst state
    cases result with
    | success value => simpa [Flapjack.Translator.Monadic.MonadBase.bind, eq] using hn value s
    | failure error => simp [Flapjack.Translator.Monadic.MonadBase.bind, eq]

private theorem preservesIgnoreBind {σ α β ε : Type} (op : M σ α ε) (next : M σ β ε)
    (h : Preserves op) (hn : Preserves next) : Preserves (ignoreBind op next) := by
  intro s
  have hs := h s
  cases eq : op s with
  | mk result state =>
    simp only [eq] at hs
    subst state
    cases result with
    | success value => simpa [ignoreBind, eq] using hn s
    | failure error => simp [ignoreBind, eq]

private theorem preservesGuard {σ ε : Type} (p : Bool) (l : LocErrInfo) (msg : ε) :
    Preserves (guard p l msg : M σ Unit (Option Locs × ε)) := by
  intro s
  cases p <;> rfl

private theorem preservesLookup {σ α : Type} (l : LocErrInfo) (kind : MlString)
    (id : Flapjack.NamespaceHOL.Ident MlString MlString)
    (env : Flapjack.NamespaceHOL.Namespace MlString MlString α) :
    Preserves (lookupStEx l kind id env : M σ α (Option Locs × MlString)) := by
  intro s
  simp [lookupStEx]
  split <;> rfl

mutual
/-- Source type checking does not change inference state. This Flapjack
    correspondence fact supports comparison with the executable checker;
    it has no separately named HOL original. -/
theorem typeNameCheckPreservesState {σ : Type} (l : LocErrInfo) (f : MlString → MlString)
    (env : TenvAbbrev) (fvs : List MlString) (t : AstT) :
    ∀ s, (typeNameCheckSubst (state := σ) l f env fvs t s).2 = s := by
  change Preserves (typeNameCheckSubst l f env fvs t)
  cases t with
  | atvar tv =>
    simp only [typeNameCheckSubst]
    exact preservesIgnoreBind _ _ (preservesGuard _ _ _) (preservesRet _)
  | attup ts =>
    simp only [typeNameCheckSubst]
    exact preservesBind _ _ (typeNameChecksPreserveState l f env fvs ts) (fun _ => preservesRet _)
  | atfun a b =>
    simp only [typeNameCheckSubst]
    exact preservesBind _ _ (typeNameCheckPreservesState l f env fvs a) (fun _ =>
      preservesBind _ _ (typeNameCheckPreservesState l f env fvs b) (fun _ => preservesRet _))
  | atapp ts tc =>
    simp only [typeNameCheckSubst]
    exact preservesBind _ _ (typeNameChecksPreserveState l f env fvs ts) (fun _ =>
      preservesBind _ _ (preservesLookup _ _ _ _) (fun _ =>
        preservesIgnoreBind _ _ (preservesGuard _ _ _) (preservesRet _)))
termination_by sizeOf t

/-- List counterpart for executable correspondence, with no separately named
    HOL original. -/
theorem typeNameChecksPreserveState {σ : Type} (l : LocErrInfo) (f : MlString → MlString)
    (env : TenvAbbrev) (fvs : List MlString) (ts : List AstT) :
    ∀ s, (typeNameCheckSubstList (state := σ) l f env fvs ts s).2 = s := by
  change Preserves (typeNameCheckSubstList l f env fvs ts)
  cases ts with
  | nil =>
    simp only [typeNameCheckSubstList]
    exact preservesRet _
  | cons t ts =>
    simp only [typeNameCheckSubstList]
    exact preservesBind _ _ (typeNameCheckPreservesState l f env fvs t) (fun _ =>
      preservesBind _ _ (typeNameChecksPreserveState l f env fvs ts) (fun _ => preservesRet _))
termination_by sizeOf ts
end

end Flapjack.Compiler.Inference.Infer.TypeNameCheck
