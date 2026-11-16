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

/-- The source list occurrence rules over the first-order relation model. -/
def coclModel (s : Spt InferT) : List InferT → Nat → Prop
  | [], _ => False
  | t :: ts, n => cocModel s t n ∨ coclModel s ts n

/-- Observe whether the executed partial worklist returns true. Its result on
    a nonterminating input is not claimed to match HOL outside `cwfs`. -/
def tcocwlModel (s : Spt InferT) (n : Nat) (work : List (List InferT)) : Prop :=
  occursWorkPartial s n work = some true

@[hol "cakeml/compiler/inference/unifyScript.sml" "tcocwl_correct"]
theorem tcocwlCorrect (s : Spt InferT) (ts : List InferT) (n : Nat)
    (hw : cwfs s) : coclModel s ts n ↔ tcocwlModel s n [ts] := by
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
  unfold tcocwlModel
  obtain ⟨b, hb, hiff⟩ := occursWorkListCorrect s hw n ts
  rw [hb]
  simp only [Option.some.injEq]
  rw [hiff]
  clear b hb hiff
  induction ts with
  | nil => simp [coclModel]
  | cons t ts ih => simp [coclModel, cocEq t, ih]

end Flapjack.Compiler.Inference.Unify
