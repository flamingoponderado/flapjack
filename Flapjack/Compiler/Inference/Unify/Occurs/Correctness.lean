module

public import Flapjack.Compiler.Inference.Unify.Occurs
public import Flapjack.Compiler.Inference.Unify.Walkstar.Encoding
public import Flapjack.HOL.Unification.Walkstar.Occurs

@[expose] public section

/-! Correctness of the occurrence worklist on well-formed substitutions. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- The source occurrence relation on encoded sparse-tree substitutions.
    Its underlying walker model is only compared with HOL under `cwfs`. -/
def cocModel (s : Spt InferT) (t : InferT) (v : Nat) : Prop :=
  Oc (sp2fm (sptMap encodeInferT s)) (encodeInferT t) v

@[hol "cakeml/compiler/inference/unifyScript.sml" "soc_encode_ts"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem socEncodeTs (s : Spt InferT) (ts : List InferT) (n : Nat)
    (hw : cwfs s) :
    Oc (sp2fm (sptMap encodeInferT s)) (encodeInferTs ts) n ↔
      ∃ t ∈ ts, cocModel s t n := by
  induction ts with
  | nil =>
    rw [ocWalking _ _ _ hw.1]
    simp [encodeInferTs, walk]
  | cons t ts ih =>
    rw [ocWalking _ _ _ hw.1]
    simp [encodeInferTs, walk, cocModel, ih]

/-- The source list occurrence rules over the first-order relation model. -/
def coclModel (s : Spt InferT) : List InferT → Nat → Prop
  | [], _ => False
  | t :: ts, n => cocModel s t n ∨ coclModel s ts n

/-- The executed partial worklist returns a Boolean agreeing with the source
    occurrence relation on well-formed substitutions. This execution result
    is not tagged as HOL's `tcocwl_correct`: the HOL operation returns a
    Boolean directly, while this one returns an `Option` for nontermination. -/
theorem occursWorkListCoclCorrect (s : Spt InferT) (ts : List InferT) (n : Nat)
    (hw : cwfs s) : ∃ b, occursWorkPartial s n [ts] = some b ∧
      (coclModel s ts n ↔ b = true) := by
  have cocEq : ∀ t, cocModel s t n ↔ tVars (tWalkstar (sp2fm s) t) n := by
    intro t
    have heq : sp2fm (sptMap encodeInferT s) =
        (sp2fm s).map2 (fun p => encodeInferT p.2) := by
      apply HolFiniteMapExact.ext_lookup
      intro key
      exact sptLookup_sptMap encodeInferT s key
    have hs : wfs (sp2fm (sptMap encodeInferT s)) := hw.1
    have hws : tWfs (sp2fm s) := by rw [heq] at hs; exact hs
    unfold cocModel
    rw [ocEqVarsWalkstar _ _ _ hs, heq, encodeWalkstar (sp2fm s) t hws]
    rfl
  obtain ⟨b, hb, hiff⟩ := occursWorkListCorrect s hw n ts
  refine ⟨b, hb, ?_⟩
  rw [hiff]
  clear b hb hiff
  induction ts with
  | nil => simp [coclModel]
  | cons t ts ih => simp [coclModel, cocEq t, ih]

end Flapjack.Compiler.Inference.Unify
