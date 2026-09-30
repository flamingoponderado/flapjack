import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact
namespace NestedDecsSupport

/-- Flapjack-specific re-export of the canonical state carrier roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end NestedDecsSupport

/-- HOL single_dec_evaluate: scope restoration changes only locals, which
state_rel intentionally excludes. The successful expression, updated-locals
body evaluation and non-Error premises are exactly the original premises;
the target declaration evaluation and related state are constructed. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "single_dec_evaluate"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem singleDecEvaluateExact {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (v : Nat) (e : CrepExpHOL width) (value : HolWordLab width)
    (he : evalCrepSemHOLExp s e = some value)
    (hp : evalCrepSemHOLProgExact
      {s with locals := s.locals.updateEq (v,value)} p = (r,s'))
    (_hnotError : r ≠ some .error) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact s (.dec v e p) = (r,t') ∧
      crepInlineStateRelExact s' t' := by
  refine ⟨{s' with locals := s'.locals.resVarEq (v,s.locals.lookup v)}, ?_, ?_⟩
  · rw [evalCrepSemHOLProgExact_dec_holShape, he]
    simp only [hp]
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Flapjack.CrepInlineExact
