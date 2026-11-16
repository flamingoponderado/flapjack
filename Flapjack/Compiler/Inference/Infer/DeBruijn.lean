module

public import Flapjack.Compiler.Inference.Infer

@[expose] public section

namespace Flapjack.Compiler.Inference.Infer

/-- The recursive list traversal used by substitution is list map. This
    supports the alternative HOL equation below. -/
private theorem substListEqMap (s : List InferT) : ∀ ts,
    inferDeBruijnSubstList s ts = ts.map (inferDeBruijnSubst s) := by
  intro ts
  induction ts with
  | nil => simp [inferDeBruijnSubstList]
  | cons t ts ih => simp [inferDeBruijnSubstList, ih]

@[hol "cakeml/compiler/inference/inferScript.sml" "infer_deBruijn_subst_alt"]
theorem inferDeBruijnSubstAlt (s : List InferT) (n : Nat) (ts : List InferT) (tn : Nat) :
    (inferDeBruijnSubst s (.varDb n) =
      if h : n < s.length then s[n] else .varDb (n - s.length)) ∧
    (inferDeBruijnSubst s (.app ts tn) = .app (ts.map (inferDeBruijnSubst s)) tn) ∧
    (inferDeBruijnSubst s (.uvar n) = .uvar n) := by
  constructor
  · by_cases h : n < s.length <;> simp [inferDeBruijnSubst, h]
  constructor
  · simp [inferDeBruijnSubst, substListEqMap]
  · simp [inferDeBruijnSubst]

end Flapjack.Compiler.Inference.Infer
