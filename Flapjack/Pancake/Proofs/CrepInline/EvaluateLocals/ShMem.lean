import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact
namespace ShMemLocalsSupport
/-- Flapjack-specific canonical state roundtrip re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end ShMemLocalsSupport

/-- ShMem case of HOL evaluate_locals_same_fdom. Loads update an existing
binding; stores preserve locals. The original result guard excludes a final
load event, whose state has empty locals. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomShMemExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (operator : WordMemOp) (name : Nat) (address : CrepExpHOL width)
    (heval : evalCrepSemHOLProgExact s (.shMem operator name address) = (r,s'))
    (hresult : match r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  classical
  rw [evalCrepSemHOLProgExact_shMem_holShape] at heval
  cases operator <;>
    dsimp only [crepIsLoadMemOp, crepShMemOpExactHOL] at heval
  all_goals
    repeat' (first | dsimp at heval | split at heval)
  all_goals
    try unfold crepShMemLoadExactHOL at heval
    try unfold crepShMemStoreExactHOL at heval
    repeat' (first | dsimp at heval | split at heval)
  all_goals
    rcases heval with ⟨rfl,rfl⟩
  all_goals
    try exact False.elim hresult
    try rfl
  all_goals
    funext key
    simp only [crepHolFdom, CrepSemHOLState.setVar, HolFiniteMapExact.updateEq]
    by_cases heq : key = name
    · subst key
      simp_all [FUPDATE_HOL]
    · simp [FUPDATE_HOL, heq]

end Flapjack.CrepInlineExact
