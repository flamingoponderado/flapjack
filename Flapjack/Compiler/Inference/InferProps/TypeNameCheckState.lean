module

public import Flapjack.Compiler.Inference.Infer.TypeNameCheckState

@[expose] public section

/-! State preservation for source type-name checking. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.Misc.Location
  Flapjack.Basis.Pure.MlString Flapjack.Translator.Monadic.MonadBase
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.Infer.TypeNameCheck

/-- Both type-name checkers preserve their input state, including on errors. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "type_name_check_subst_state"]
theorem typeNameCheckSubstState {σ : Type} :
    (∀ (t : AstT) (l : LocErrInfo) (err : MlString → MlString) (env : TenvAbbrev)
      (fvs : List MlString) (s : σ) (r : Exc SemanticT (Option Locs × MlString)) (s' : σ),
      typeNameCheckSubst l err env fvs t s = (r, s') → s = s') ∧
    (∀ (ts : List AstT) (l : LocErrInfo) (err : MlString → MlString) (env : TenvAbbrev)
      (fvs : List MlString) (s : σ) (r : Exc (List SemanticT) (Option Locs × MlString)) (s' : σ),
      typeNameCheckSubstList l err env fvs ts s = (r, s') → s = s') := by
  constructor
  · intro t l err env fvs s r s' run
    have result := congrArg Prod.snd run
    rw [typeNameCheckPreservesState l err env fvs t s] at result
    exact result
  · intro ts l err env fvs s r s' run
    have result := congrArg Prod.snd run
    rw [typeNameChecksPreserveState l err env fvs ts s] at result
    exact result

end Flapjack.Compiler.Inference.InferProps
