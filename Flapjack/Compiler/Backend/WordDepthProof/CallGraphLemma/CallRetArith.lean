import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.CallRetFacts

/-!
# `max_depth_call_graph_lemma`: arithmetic of the returning `Call`

Flapjack infrastructure: `option_le` comparisons between the callee/return
bounds and the call-graph bound of a returning call, without and with an
exception handler (the handler frame costs 3 more words). Variables:
`m` = `stack_max`, `S` = `stack_size stack`, `Ln`/`Ld` = caller/callee frame
sizes, `G` = `max_depth_graphs`, `X`/`R`/`H` = callee/return/handler depths.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps

/-- Callee bound below the goal bound (no handler). -/
theorem retN_callee (m S Ln Ld G X R : Option Nat) :
    optionLe
      (optionMap₂ max
        (wordSemOptionMax (wordSemOptionMax m (wordSemOptionAdd Ln S))
          (wordSemOptionAdd (wordSemOptionAdd Ln S) Ld))
        (optionMap₂ (· + ·) (wordSemOptionAdd Ln S)
          (optionMap₂ max (optionMap₂ max Ld (optionMap₂ max X (some 0))) X)))
      (optionMap₂ max m (optionMap₂ (· + ·) S (optionMap₂ max G
        (optionMap₂ max (optionMap₂ (· + ·) Ln (optionMap₂ (· + ·) Ld (some 0)))
          (optionMap₂ max (optionMap₂ (· + ·) Ln X) R))))) := by
  rcases m with _ | m <;> rcases S with _ | S <;> rcases Ln with _ | Ln <;>
    rcases Ld with _ | Ld <;> rcases G with _ | G <;> rcases X with _ | X <;>
    rcases R with _ | R <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe]
  all_goals omega

/-- Return-continuation bound below the goal bound (no handler). -/
theorem retN_return (m S Ln Ld G X R : Option Nat) :
    optionLe
      (optionMap₂ max
        (optionMap₂ max
          (wordSemOptionMax (wordSemOptionMax m (wordSemOptionAdd Ln S))
            (wordSemOptionAdd (wordSemOptionAdd Ln S) Ld))
          (optionMap₂ (· + ·) (wordSemOptionAdd Ln S)
            (optionMap₂ max (optionMap₂ max Ld (optionMap₂ max X (some 0))) X)))
        (optionMap₂ (· + ·) S (optionMap₂ max G R)))
      (optionMap₂ max m (optionMap₂ (· + ·) S (optionMap₂ max G
        (optionMap₂ max (optionMap₂ (· + ·) Ln (optionMap₂ (· + ·) Ld (some 0)))
          (optionMap₂ max (optionMap₂ (· + ·) Ln X) R))))) := by
  rcases m with _ | m <;> rcases S with _ | S <;> rcases Ln with _ | Ln <;>
    rcases Ld with _ | Ld <;> rcases G with _ | G <;> rcases X with _ | X <;>
    rcases R with _ | R <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe]
  all_goals omega

/-- Callee bound below the goal bound (with handler). -/
theorem retS_callee (m S Ln Ld G X R H : Option Nat) :
    optionLe
      (optionMap₂ max
        (wordSemOptionMax (wordSemOptionMax m (wordSemOptionAdd (Ln.map (3 + ·)) S))
          (wordSemOptionAdd (wordSemOptionAdd (Ln.map (3 + ·)) S) Ld))
        (optionMap₂ (· + ·) (wordSemOptionAdd (Ln.map (3 + ·)) S)
          (optionMap₂ max (optionMap₂ max Ld (optionMap₂ max X (some 0))) X)))
      (optionMap₂ max m (optionMap₂ (· + ·) S (optionMap₂ max G
        (optionMap₂ max (optionMap₂ (· + ·) Ln ((optionMap₂ (· + ·) Ld (some 0)).map (3 + ·)))
          (optionMap₂ max (optionMap₂ (· + ·) Ln (X.map (3 + ·))) (optionMap₂ max H R)))))) := by
  rcases m with _ | m <;> rcases S with _ | S <;> rcases Ln with _ | Ln <;>
    rcases Ld with _ | Ld <;> rcases G with _ | G <;> rcases X with _ | X <;>
    rcases R with _ | R <;> rcases H with _ | H <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe, Option.map]
  all_goals omega

/-- Return-continuation bound below the goal bound (with handler). -/
theorem retS_return (m S Ln Ld G X R H : Option Nat) :
    optionLe
      (optionMap₂ max
        (optionMap₂ max
          (wordSemOptionMax (wordSemOptionMax m (wordSemOptionAdd (Ln.map (3 + ·)) S))
            (wordSemOptionAdd (wordSemOptionAdd (Ln.map (3 + ·)) S) Ld))
          (optionMap₂ (· + ·) (wordSemOptionAdd (Ln.map (3 + ·)) S)
            (optionMap₂ max (optionMap₂ max Ld (optionMap₂ max X (some 0))) X)))
        (optionMap₂ (· + ·) S (optionMap₂ max G R)))
      (optionMap₂ max m (optionMap₂ (· + ·) S (optionMap₂ max G
        (optionMap₂ max (optionMap₂ (· + ·) Ln ((optionMap₂ (· + ·) Ld (some 0)).map (3 + ·)))
          (optionMap₂ max (optionMap₂ (· + ·) Ln (X.map (3 + ·))) (optionMap₂ max H R)))))) := by
  rcases m with _ | m <;> rcases S with _ | S <;> rcases Ln with _ | Ln <;>
    rcases Ld with _ | Ld <;> rcases G with _ | G <;> rcases X with _ | X <;>
    rcases R with _ | R <;> rcases H with _ | H <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe, Option.map]
  all_goals omega

/-- Exception-handler continuation bound below the goal bound. -/
theorem retS_handler (m S Ln Ld G X R H : Option Nat) :
    optionLe
      (optionMap₂ max
        (optionMap₂ max
          (wordSemOptionMax (wordSemOptionMax m (wordSemOptionAdd (Ln.map (3 + ·)) S))
            (wordSemOptionAdd (wordSemOptionAdd (Ln.map (3 + ·)) S) Ld))
          (optionMap₂ (· + ·) (wordSemOptionAdd (Ln.map (3 + ·)) S)
            (optionMap₂ max (optionMap₂ max Ld (optionMap₂ max X (some 0))) X)))
        (optionMap₂ (· + ·) S (optionMap₂ max G H)))
      (optionMap₂ max m (optionMap₂ (· + ·) S (optionMap₂ max G
        (optionMap₂ max (optionMap₂ (· + ·) Ln ((optionMap₂ (· + ·) Ld (some 0)).map (3 + ·)))
          (optionMap₂ max (optionMap₂ (· + ·) Ln (X.map (3 + ·))) (optionMap₂ max H R)))))) := by
  rcases m with _ | m <;> rcases S with _ | S <;> rcases Ln with _ | Ln <;>
    rcases Ld with _ | Ld <;> rcases G with _ | G <;> rcases X with _ | X <;>
    rcases R with _ | R <;> rcases H with _ | H <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe, Option.map]
  all_goals omega

end Flapjack.Compiler.Backend.WordDepthProof
