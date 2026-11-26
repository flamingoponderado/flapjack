module

public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer

mutual
/-- Structural induction helper for the original type-check monotonicity result. -/
private theorem checkMonoType (t : InferT) (uvs : Nat → Prop) (tvs : Nat)
    (h : checkT tvs uvs t) (uvs' : Nat → Prop) (sub : ∀ v, uvs v → uvs' v) :
    checkT tvs uvs' t := by
  cases t with
  | varDb n => simpa using h
  | uvar n => exact (checkT_uvar tvs n uvs').mpr (sub n ((checkT_uvar tvs n uvs).mp h))
  | app ts tc =>
    exact (checkT_app tvs tc uvs' ts).mpr
      (checkMonoList ts uvs tvs ((checkT_app tvs tc uvs ts).mp h) uvs' sub)
termination_by sizeOf t

/-- List recursion used by type-check monotonicity for applications. -/
private theorem checkMonoList (ts : List InferT) (uvs : Nat → Prop) (tvs : Nat)
    (h : checkTList tvs uvs ts) (uvs' : Nat → Prop) (sub : ∀ v, uvs v → uvs' v) :
    checkTList tvs uvs' ts := by
  cases ts with
  | nil => simp
  | cons t ts =>
    have h' := (checkTList_cons tvs uvs t ts).mp h
    exact (checkTList_cons tvs uvs' t ts).mpr
      ⟨checkMonoType t uvs tvs h'.1 uvs' sub, checkMonoList ts uvs tvs h'.2 uvs' sub⟩
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_more5"]
theorem checkTMore5 :
    (∀ t uvs tvs, checkT tvs uvs t → ∀ uvs', (∀ v, uvs v → uvs' v) → checkT tvs uvs' t) ∧
    (∀ (ts : List InferT) uvs tvs, (∀ t ∈ ts, checkT tvs uvs t) →
      ∀ uvs', (∀ v, uvs v → uvs' v) → ∀ t ∈ ts, checkT tvs uvs' t) := by
  constructor
  · exact checkMonoType
  · intro ts uvs tvs h uvs' sub t ht
    exact checkMonoType t uvs tvs (h t ht) uvs' sub

mutual
/-- Structural induction for increasing the bound on de Bruijn variables. -/
private theorem checkBoundType (t : InferT) (tvs : Nat) (uvs : Nat → Prop)
    (h : checkT tvs uvs t) (extra : Nat) : checkT (extra + tvs) uvs t := by
  cases t with
  | varDb n =>
    have hn : n < tvs := by simpa using h
    have : n < extra + tvs := by omega
    simpa using this
  | uvar n => simpa using h
  | app ts tc =>
    exact (checkT_app (extra + tvs) tc uvs ts).mpr
      (checkBoundList ts tvs uvs ((checkT_app tvs tc uvs ts).mp h) extra)
termination_by sizeOf t

/-- List recursion for increasing the bound on de Bruijn variables. -/
private theorem checkBoundList (ts : List InferT) (tvs : Nat) (uvs : Nat → Prop)
    (h : checkTList tvs uvs ts) (extra : Nat) : checkTList (extra + tvs) uvs ts := by
  cases ts with
  | nil => simp
  | cons t ts =>
    have hs := (checkTList_cons tvs uvs t ts).mp h
    exact (checkTList_cons (extra + tvs) uvs t ts).mpr
      ⟨checkBoundType t tvs uvs hs.1 extra, checkBoundList ts tvs uvs hs.2 extra⟩
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_more2"]
theorem checkTMore2 :
    (∀ t tvs uvs, checkT tvs uvs t → ∀ extra, checkT (extra + tvs) uvs t) ∧
    (∀ (ts : List InferT) tvs uvs, (∀ t ∈ ts, checkT tvs uvs t) →
      ∀ extra t, t ∈ ts → checkT (extra + tvs) uvs t) := by
  constructor
  · exact checkBoundType
  · intro ts tvs uvs h extra t ht
    exact checkBoundType t tvs uvs (h t ht) extra

/-- Original `check_t_more3`: checking against the first `uvs` unification
variables also succeeds against the first `uvs + uvs'`. HOL's `count uvs` is
the predicate `fun k => k < uvs` on the `Nat → Prop` uvar carrier. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_more3"]
theorem checkTMore3 :
    (∀ t uvs tvs, checkT tvs (fun k => k < uvs) t →
      ∀ uvs', checkT tvs (fun k => k < (uvs + uvs')) t) ∧
    (∀ (ts : List InferT) uvs tvs, (∀ t ∈ ts, checkT tvs (fun k => k < uvs) t) →
      ∀ uvs', ∀ t ∈ ts, checkT tvs (fun k => k < (uvs + uvs')) t) := by
  constructor
  · intro t uvs tvs h uvs'
    exact checkMonoType t _ tvs h _ (fun v hv => by omega)
  · intro ts uvs tvs h uvs' t ht
    exact checkMonoType t _ tvs (h t ht) _ (fun v hv => by omega)

/-- Original `check_t_more4`: raising the uvar bound keeps the check. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_more4"]
theorem checkTMore4 :
    (∀ t uvs tvs, checkT tvs (fun k => k < uvs) t →
      ∀ uvs', uvs ≤ uvs' → checkT tvs (fun k => k < uvs') t) ∧
    (∀ (ts : List InferT) uvs tvs, (∀ t ∈ ts, checkT tvs (fun k => k < uvs) t) →
      ∀ uvs', uvs ≤ uvs' → ∀ t ∈ ts, checkT tvs (fun k => k < uvs') t) := by
  constructor
  · intro t uvs tvs h uvs' hle
    exact checkMonoType t _ tvs h _ (fun v hv => by omega)
  · intro ts uvs tvs h uvs' hle t ht
    exact checkMonoType t _ tvs (h t ht) _ (fun v hv => by omega)

/-- Original `check_t_more`: a type checked against no uvars is checked against
any uvar set. HOL's empty set `{}` is the empty predicate. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_more"]
theorem checkTMore :
    (∀ (t : InferT) tvs, checkT tvs (fun _ => False) t → ∀ uvs, checkT tvs uvs t) ∧
      (∀ (ts : List InferT) tvs, (∀ t ∈ ts, checkT tvs (fun _ => False) t) →
        ∀ uvs, ∀ t ∈ ts, checkT tvs uvs t) := by
  constructor
  · intro t tvs h uvs
    exact checkMonoType t (fun _ => False) tvs h uvs (fun v hv => hv.elim)
  · intro ts tvs h uvs t ht
    exact checkMonoType t (fun _ => False) tvs (h t ht) uvs (fun v hv => hv.elim)

/-- Original `check_s_more2`: a substitution checked against the first `uvs`
    unification variables is checked against the first `uvs'`. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_s_more2"
  (fmap_as_finite_support_parameters := [s])]
theorem checkSMore2 {α : Type} (tvs : Nat) (s : HolFiniteMapExact α InferT) (uvs : Nat) :
    checkS tvs (fun k => k < uvs) s →
      ∀ uvs', uvs ≤ uvs' → checkS tvs (fun k => k < uvs') s := by
  intro h uvs' hle uv hmem
  exact checkTMore4.1 _ uvs tvs (h uv hmem) uvs' hle

/-- The canonical substitution map survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_checkSMore2_s {α : Type}
    (s : HolFiniteMapExact α InferT) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s := by
  cases s
  exact ⟨rfl, rfl, rfl⟩

/-- Original `check_s_more3`: enlarging the uvar set keeps the substitution
    check. HOL's `⊆` is pointwise implication. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_s_more3"
  (fmap_as_finite_support_parameters := [s])]
theorem checkSMore3 {α : Type} (tvs : Nat) (s : HolFiniteMapExact α InferT)
    (uvs : Nat → Prop) :
    checkS tvs uvs s → ∀ uvs', (∀ v, uvs v → uvs' v) → checkS tvs uvs' s := by
  intro h uvs' hsub uv hmem
  exact checkTMore5.1 _ uvs tvs (h uv hmem) uvs' hsub

/-- The canonical substitution map survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_checkSMore3_s {α : Type}
    (s : HolFiniteMapExact α InferT) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s := by
  cases s
  exact ⟨rfl, rfl, rfl⟩

/-- Original `check_s_more5`: the same enlargement fact with the set relation
    as a separate premise. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_s_more5"
  (fmap_as_finite_support_parameters := [s])]
theorem checkSMore5 {α : Type} (s : HolFiniteMapExact α InferT) (uvs : Nat → Prop)
    (tvs : Nat) (uvs' : Nat → Prop) : checkS tvs uvs s → (∀ v, uvs v → uvs' v) →
      checkS tvs uvs' s := by
  intro h hsub uv hmem
  exact checkTMore5.1 _ uvs tvs (h uv hmem) uvs' hsub

/-- The canonical substitution map survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_checkSMore5_s {α : Type}
    (s : HolFiniteMapExact α InferT) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s := by
  cases s
  exact ⟨rfl, rfl, rfl⟩

end Flapjack.Compiler.Inference.InferProps
