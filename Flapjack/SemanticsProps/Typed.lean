import Flapjack.SemanticsHOL.Typed
import Flapjack.SemanticsProps.Determinism

/-! Properties of the explicitly post-parse source-semantics infrastructure. -/
namespace Flapjack.SemanticsProps
open Flapjack.SemanticsHOL Flapjack.AstHOL

/-- Flapjack post-parse property: whenever the encoded type check accepts a
parsed program, its observable behavior set contains exactly one behavior.
The absence of `Fail` additionally requires the unported type-soundness
theorem and is not assumed here. -/
theorem semanticsFromParsed_execute_singleton {σ : Type} (st : SourceState σ)
    (prelude : List Dec) (parsed : Option (List Dec)) (behaviors : HolBehaviour → Prop)
    (h : semanticsFromParsed st prelude parsed = .execute behaviors) :
    ∃ b, behaviors = fun other => other = b := by
  classical
  cases parsed with
  | none => simp [semanticsFromParsed] at h
  | some prog =>
    by_cases typed : canTypeProg st (prelude ++ prog)
    · simp [semanticsFromParsed, typed] at h
      subst behaviors
      obtain ⟨behavior, hb⟩ := semanticsProg_total st.semSt st.semEnv (prelude ++ prog)
      refine ⟨behavior, ?_⟩
      funext other
      apply propext
      constructor
      · intro ho
        exact semanticsProg_deterministic st.semSt st.semEnv (prelude ++ prog) other behavior ⟨ho, hb⟩
      · intro equal
        subst other
        exact hb
    · simp [semanticsFromParsed, typed] at h

end Flapjack.SemanticsProps
