module

public import Flapjack.Compiler.Backend.Semantics.DataProps.SemanticsPrefix
public import Flapjack.SemanticsProps.Implements
public import Flapjack.HolRef

@[expose] public section

/-!
# Resource-limit behaviour refinement for the data-language semantics

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:2201`
`Resource_limit_hit_implements_semantics`: the single behaviour "terminate with
`Resource_limit_hit` and the starting FFI trace" is implemented by the
data-language whole-program semantics, in the resource-limit-extended sense of
`semanticsProps$implements`. The proof is HOL's: case on the semantics and use
`semantics_Term_IMP_PREFIX` for a terminating run and
`semantics_Div_IMP_LPREFIX` for a divergent one.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticsPropsHOL

/-- Exact HOL `Resource_limit_hit_implements_semantics`
    (`dataPropsScript.sml:2201`): the resource-limit-hit behaviour with the
    initial FFI trace is implemented by the data-language semantics. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml"
  "Resource_limit_hit_implements_semantics"]
theorem resourceLimitHitImplementsSemantics {C F : Type} (ffi : HolFfiState F)
    (prog : List (Nat × Nat × DataLang.Prog)) (co : CompileOracle C) (cc : Compiler C)
    (lim : Limits) (ss : Spt Nat) (start : Nat) :
    implementsHOL (fun behavior => behavior = .terminate .resourceLimitHit ffi.ioEvents)
      (fun behavior => behavior = semantics ffi (sptFromAList prog) co cc lim ss start) := by
  intro notFail result hresult
  unfold extendWithResourceLimitHOL
  cases semEq : semantics ffi (sptFromAList prog) co cc lim ss start with
  | fail =>
    exact absurd semEq.symm notFail
  | terminate outcome events =>
    refine Or.inr (Or.inl ⟨ffi.ioEvents, outcome, events, hresult, ?_, ?_⟩)
    · rfl
    · exact semanticsTermImpPrefix ffi (sptFromAList prog) co cc lim ss start outcome events semEq
  | diverge trace =>
    refine Or.inr (Or.inr ⟨ffi.ioEvents, trace, hresult, ?_, ?_⟩)
    · rfl
    · exact semanticsDivImpLprefix ffi (sptFromAList prog) co cc lim ss start trace semEq

end Flapjack.Compiler.Backend.DataProps
