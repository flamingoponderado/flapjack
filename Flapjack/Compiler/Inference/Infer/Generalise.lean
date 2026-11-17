module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.HOL.Transfer.Fmsp.Operations
public import Flapjack.HOL.Transfer.Fmsp.Inverse

@[expose] public section

/-! Finite-map generalization and its executable sparse-tree correspondence. -/
namespace Flapjack.Compiler.Inference.Infer.Generalise
open Flapjack.HOL.Transfer.Fmsp

mutual
/-- Source-shaped generalization over canonical finite maps. This is not tagged
    as `generalise_def`: its finite-map input and tuple result require a
    representation qualifier that has not yet been established. -/
def generaliseMap (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat) :
    InferT → Nat × HolFiniteMapExact Nat Nat × InferT
  | .app ts name =>
    let (count, subst, ts) := generaliseListMap minimum next subst ts
    (count, subst, .app ts name)
  | .uvar n => match subst.lookup n with
    | some v => (0, subst, .varDb v)
    | none => if minimum ≤ n then (1, subst.updateEq (n, next), .varDb next)
      else (0, subst, .uvar n)
  | .varDb n => (0, subst, .varDb n)
termination_by t => sizeOf t

/-- The source-shaped list traversal uses the same finite-map carrier as
    `generaliseMap`; its source tag awaits the same tuple qualifier. -/
def generaliseListMap (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat) :
    List InferT → Nat × HolFiniteMapExact Nat Nat × List InferT
  | [] => (0, subst, [])
  | t :: ts =>
    let (count, subst, t) := generaliseMap minimum next subst t
    let (count', subst, ts) := generaliseListMap minimum (count + next) subst ts
    (count + count', subst, t :: ts)
termination_by ts => sizeOf ts
end

mutual
/-- The executable sparse-tree operation agrees with the finite-map model on
    every input, preserving the complete count, substitution and type. -/
theorem generaliseCorresponds (minimum next : Nat) (subst : Spt Nat) (t : InferT) :
    generaliseMap minimum next (sp2fm subst) t =
      let (count, out, typ) := Infer.generalise minimum next subst t
      (count, sp2fm out, typ) := by
  cases t with
  | varDb n => simp [generaliseMap, Infer.generalise]
  | uvar n =>
    have look : (sp2fm subst).lookup n = sptLookup n subst := rfl
    simp only [generaliseMap, Infer.generalise, look]
    cases h : sptLookup n subst with
    | none =>
      by_cases hm : minimum ≤ n
      · simp only [hm, ↓reduceIte, Prod.mk.injEq, true_and, and_true]
        exact (sp2fmThm (α := Nat) n next subst).2.symm
      · simp [hm]
    | some v => simp
  | app ts name =>
    simp only [generaliseMap, Infer.generalise]
    have h := generaliseListCorresponds minimum next subst ts
    cases result : Infer.generaliseList minimum next subst ts with
    | mk count rest =>
      cases rest with
      | mk out types => simp [result] at h; simp [h]
termination_by sizeOf t

/-- The list traversal correspondence preserves the complete output triple. -/
theorem generaliseListCorresponds (minimum next : Nat) (subst : Spt Nat) (ts : List InferT) :
    generaliseListMap minimum next (sp2fm subst) ts =
      let (count, out, types) := Infer.generaliseList minimum next subst ts
      (count, sp2fm out, types) := by
  cases ts with
  | nil => simp [generaliseListMap, Infer.generaliseList]
  | cons t ts =>
    simp only [generaliseListMap, Infer.generaliseList]
    have h := generaliseCorresponds minimum next subst t
    cases first : Infer.generalise minimum next subst t with
    | mk count rest =>
      cases rest with
      | mk mid typ =>
        simp only [first] at h ⊢
        rw [h]
        have tail := generaliseListCorresponds minimum (count + next) mid ts
        cases second : Infer.generaliseList minimum (count + next) mid ts with
        | mk count' rest =>
          cases rest with
          | mk out types => simp [second] at tail; simp [tail]
termination_by sizeOf ts
end

/-- Every finite map has the same lookups after conversion through the sparse
    representation; this is the input codec for the generalization proof. -/
private theorem finiteMapRoundtrip (subst : HolFiniteMapExact Nat Nat) :
    sp2fm (fm2sp subst) = subst := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  exact lookupFm2sp key subst

/-- The complete finite-map model can be computed through the executable
    generalizer for any input map, with its entire output map reconstructed. -/
theorem generaliseFromFiniteMap (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (t : InferT) :
    generaliseMap minimum next subst t =
      let (count, out, typ) := Infer.generalise minimum next (fm2sp subst) t
      (count, sp2fm out, typ) := by
  simpa only [finiteMapRoundtrip] using generaliseCorresponds minimum next (fm2sp subst) t

/-- The list case has the same unconditional complete output correspondence. -/
theorem generaliseListFromFiniteMap (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (ts : List InferT) :
    generaliseListMap minimum next subst ts =
      let (count, out, types) := Infer.generaliseList minimum next (fm2sp subst) ts
      (count, sp2fm out, types) := by
  simpa only [finiteMapRoundtrip] using generaliseListCorresponds minimum next (fm2sp subst) ts

end Flapjack.Compiler.Inference.Infer.Generalise
