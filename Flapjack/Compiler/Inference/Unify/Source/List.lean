module

public import Flapjack.Compiler.Inference.Unify.Source

@[expose] public section

/-! Source list-unifier equation on well-formed substitutions. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Source-shaped list unifier. It remains untagged because agreement with
    HOL's selected unifier outside the well-formedness guard is not established;
    the finite-map representation is internal to the sparse-tree result. -/
noncomputable def cunifylModel (s : Spt InferT) (xs ys : List InferT) : Option (Spt InferT) :=
  (sunifyModel (sptMap encodeInferT s) (encodeInferTs xs) (encodeInferTs ys)).map (sptMap decodeInferT)

private theorem listMap (s : Spt InferT) (xs ys : List InferT) (hw : cwfs s) :
    (cunifylModel s xs ys).map sp2fm = tsUnifyModel (sp2fm s) xs ys := by
  have hws : tWfs (sp2fm s) := by
    change wfs (encodeSubst (sp2fm s))
    rw [← sparseEncode]
    exact hw.1
  rw [← tsUnifyModelEncoding xs ys (sp2fm s) hws]
  simp only [cunifylModel, sunifyModel, Option.map_map, sparseEncode]
  have hwf : wfs (encodeSubst (sp2fm s)) := hws
  rw [specifiedUnifyEqAux _ _ _ hwf]
  cases h : tunifyAux (encodeSubst (sp2fm s)) (encodeInferTs xs) (encodeInferTs ys) with
  | none => rfl
  | some result =>
    simp only [Option.map_some, Option.some.injEq]
    exact sparseDecode result

private theorem listWf (s out : Spt InferT) (xs ys : List InferT)
    (h : cunifylModel s xs ys = some out) : sptWf out = true := by
  unfold cunifylModel sunifyModel at h
  cases hr : specifiedUnify (sp2fm (sptMap encodeInferT s)) (encodeInferTs xs) (encodeInferTs ys) with
  | none => simp [hr] at h
  | some fm =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    subst out
    rw [sptWfMap]
    exact wfFm2sp _

private theorem optionTreesEq (left right : Option (Spt InferT))
    (lm : ∀ t, left = some t → sptWf t = true)
    (rm : ∀ t, right = some t → sptWf t = true)
    (h : left.map sp2fm = right.map sp2fm) : left = right := by
  cases left with
  | none => cases right <;> simp_all
  | some l =>
    cases right with
    | none => simp at h
    | some r =>
      simp only [Option.map_some, Option.some.injEq] at h
      have eq : l = r := (sptEqThm l r ⟨lm l rfl, rm r rfl⟩).mpr (fun k => congrArg (fun m => m.lookup k) h)
      rw [eq]

@[hol "cakeml/compiler/inference/unifyScript.sml" "cunifyl_thm"]
theorem cunifylThmModel (s : Spt InferT) (xs ys : List InferT) (hw : cwfs s) :
    cunifylModel s xs ys = match xs, ys with
      | [], [] => some s
      | x :: xt, y :: yt => (cunifyModel s x y).bind (fun mid => cunifylModel mid xt yt)
      | _, _ => none := by
  cases xs with
  | nil =>
    cases ys with
    | nil =>
      apply optionTreesEq _ _ (fun t => listWf s t [] []) ?_ ?_
      · intro t ht; cases ht; exact hw.2
      · simpa [tsUnifyModel] using listMap s [] [] hw
    | cons y yt =>
      apply optionTreesEq _ _ (fun t => listWf s t [] (y :: yt)) ?_ ?_
      · intro t ht; contradiction
      · simpa [tsUnifyModel] using listMap s [] (y :: yt) hw
  | cons x xt =>
    cases ys with
    | nil =>
      apply optionTreesEq _ _ (fun t => listWf s t (x :: xt) []) ?_ ?_
      · intro t ht; contradiction
      · simpa [tsUnifyModel] using listMap s (x :: xt) [] hw
    | cons y yt =>
      cases head : cunifyModel s x y with
      | none =>
        have hm := cunifyModelMap s x y hw
        rw [head] at hm
        apply optionTreesEq _ _ (fun t => listWf s t (x :: xt) (y :: yt)) ?_ ?_
        · intro t ht; simp [head] at ht
        · simpa [tsUnifyModel, ← hm, head] using listMap s (x :: xt) (y :: yt) hw
      | some mid =>
        have hmid := cunifyPreservesCwfsModel s x y mid ⟨hw, head⟩
        have hm := cunifyModelMap s x y hw
        rw [head] at hm
        apply optionTreesEq _ _ (fun t => listWf s t (x :: xt) (y :: yt)) ?_ ?_
        · intro t ht
          simp only [head, Option.bind] at ht
          exact listWf mid t xt yt ht
        · simp only [head, Option.bind]
          have first := listMap s (x :: xt) (y :: yt) hw
          simp only [tsUnifyModel, ← hm, Option.map_some, Option.bind] at first
          exact first.trans (listMap mid xt yt hmid).symm

end Flapjack.Compiler.Inference.Unify
