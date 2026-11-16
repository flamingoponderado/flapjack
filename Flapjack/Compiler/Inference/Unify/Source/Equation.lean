module

public import Flapjack.Compiler.Inference.Unify.Source.List
public import Flapjack.Compiler.Inference.Unify.Occurs.Correctness
public import Flapjack.HOL.Transfer.Fmsp.Operations

@[expose] public section

/-! Source single-type unification equation on well-formed substitutions. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

private noncomputable def rhs (s : Spt InferT) (a b : InferT) : Option (Spt InferT) := by
  classical
  exact match cwalkModel s a, cwalkModel s b with
    | .varDb x, .varDb y => if x = y then some s else none
    | .varDb x, .uvar v | .uvar v, .varDb x => some (sptInsert v (.varDb x) s)
    | .app xs x, .app ys y => if x = y then cunifylModel s xs ys else none
    | .app xs x, .uvar v | .uvar v, .app xs x =>
      if ∃ t ∈ xs, cocModel s t v then none else some (sptInsert v (.app xs x) s)
    | .uvar v, .uvar w => if v = w then some s else some (sptInsert v (.uvar w) s)
    | _, _ => none

private theorem rhsWf (s : Spt InferT) (a b : InferT) (hw : cwfs s) :
    ∀ out, rhs s a b = some out → sptWf out = true := by
  classical
  intro out result
  unfold rhs at result
  cases ha : cwalkModel s a <;> cases hb : cwalkModel s b <;> simp only [ha, hb] at result
  case varDb.varDb =>
    split at result
    · simp only [Option.some.injEq] at result
      subst out
      exact hw.2
    · contradiction
  case uvar.uvar =>
    split at result <;> simp only [Option.some.injEq] at result <;> subst out
    · exact hw.2
    · exact sptWfInsert _ _ _ hw.2
  case varDb.app | app.varDb => simp at result
  case varDb.uvar | uvar.varDb =>
    cases result
    exact sptWfInsert _ _ _ hw.2
  case app.uvar | uvar.app =>
    split at result
    · contradiction
    · cases result
      exact sptWfInsert _ _ _ hw.2
  case app.app =>
    split at result
    · exact cunifylModelTreeWf _ _ _ _ result
    · contradiction

private theorem occApp (s : Spt InferT) (xs : List InferT) (name v : Nat) (hw : cwfs s) :
    tOc (sp2fm s) (.app xs name) v ↔ ∃ t ∈ xs, cocModel s t v := by
  have h := cocThm s (.app xs name) v hw
  simp only [cwalkModel, tWalkEqn] at h
  change Oc (sp2fm (sptMap encodeInferT s)) (encodeInferT (.app xs name)) v ↔ _ at h
  change Oc (encodeSubst (sp2fm s)) (encodeInferT (.app xs name)) v ↔ _
  rwa [← sparseEncode]

private theorem rhsMap (s : Spt InferT) (a b : InferT) (hw : cwfs s) :
    (rhs s a b).map sp2fm = tUnifyModel (sp2fm s) a b := by
  classical
  have hws : tWfs (sp2fm s) := by
    change wfs (encodeSubst (sp2fm s))
    rw [← sparseEncode]
    exact hw.1
  have insertMap : ∀ v t, sp2fm (sptInsert v t s) = (sp2fm s).updateEq (v, t) := by
    intro v t
    exact (sp2fmThm (α := InferT) v t s).2
  have dbNotOc : ∀ v n, ¬ tOc (sp2fm s) (.varDb n) v := by
    intro v n
    change ¬ Oc (encodeSubst (sp2fm s)) (encodeInferT (.varDb n)) v
    have he : wfs (encodeSubst (sp2fm s)) := hws
    rw [ocWalking _ _ _ he]
    simp [encodeInferT, walk]
  rw [tUnifyModelEquation _ _ _ hws]
  change (rhs s a b).map sp2fm = (match cwalkModel s a, cwalkModel s b with
    | .uvar v1, .uvar v2 => some (if v1 = v2 then sp2fm s else (sp2fm s).updateEq (v1, .uvar v2))
    | .uvar v, other => tExtSCheck (sp2fm s) v other
    | other, .uvar v => tExtSCheck (sp2fm s) v other
    | .app xs x, .app ys y => if x = y then tsUnifyModel (sp2fm s) xs ys else none
    | .varDb x, .varDb y => if x = y then some (sp2fm s) else none
    | _, _ => none)
  unfold rhs
  cases cwalkModel s a <;> cases cwalkModel s b <;> simp only
  case varDb.varDb => split <;> simp_all
  case varDb.app | app.varDb => rfl
  case varDb.uvar | uvar.varDb =>
    rw [tExtSCheckEqn]
    simp [dbNotOc, insertMap]
  case app.app =>
    split
    · exact cunifylModelMap s _ _ hw
    · rfl
  case app.uvar | uvar.app =>
    rw [tExtSCheckEqn, occApp s _ _ _ hw]
    split <;> simp_all
  case uvar.uvar =>
    split <;> simp_all

private theorem sourceEquation (s : Spt InferT) (a b : InferT) (hw : cwfs s) :
    cunifyModel s a b = rhs s a b := by
  apply optionTreesEq _ _ (fun out => cunifyModelTreeWf s out a b) (rhsWf s a b hw)
  exact (cunifyModelMap s a b).trans (rhsMap s a b hw).symm

@[hol "cakeml/compiler/inference/unifyScript.sml" "cunify_thm"]
theorem cunifyThmModel (s : Spt InferT) (a b : InferT) (hw : cwfs s) :
    cunifyModel s a b = by
      classical
      exact match cwalkModel s a, cwalkModel s b with
        | .varDb x, .varDb y => if x = y then some s else none
        | .varDb x, .uvar v | .uvar v, .varDb x => some (sptInsert v (.varDb x) s)
        | .app xs x, .app ys y => if x = y then cunifylModel s xs ys else none
        | .app xs x, .uvar v | .uvar v, .app xs x =>
          if ∃ t ∈ xs, cocModel s t v then none else some (sptInsert v (.app xs x) s)
        | .uvar v, .uvar w => if v = w then some s else some (sptInsert v (.uvar w) s)
        | _, _ => none :=
  sourceEquation s a b hw

end Flapjack.Compiler.Inference.Unify
