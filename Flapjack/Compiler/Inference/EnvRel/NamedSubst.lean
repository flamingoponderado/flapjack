module

public import Flapjack.Compiler.Inference.EnvRel
public import Flapjack.TypeSystemHOL.TypeNames
public import Flapjack.FiniteMap.AlistExact

@[expose] public section

/-! Conversion of named type substitutions. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString

/-- A canonical map built from an association list has first-match lookup. -/
private theorem lookupAlistMap (entries : List (MlString × SemanticT)) (key : MlString) :
    (HolFiniteMapExact.alistToFmap entries).lookup key = entries.lookup key := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : key = k
    · subst key
      rw [HolFiniteMapExact.lookup_alistToFmap_head]
      simp [List.lookup]
    · rw [HolFiniteMapExact.lookup_alistToFmap_tail (key := key) _ _ h]
      have hb : (key == k) = false := by simp [h]
      simpa [List.lookup, hb] using ih

/-- Zipping names with mapped values maps the result of first-match lookup. -/
private theorem lookupZipMap (names : List MlString) (values : List InferT)
    (key : MlString) :
    ((names.zip (values.map convertT)).lookup key) =
      ((names.zip values).lookup key).map convertT := by
  induction names generalizing values with
  | nil => rfl
  | cons name names ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      by_cases h : key = name
      · subst key; simp
      · have hb : (key == name) = false := by simp [h]
        simpa [List.lookup, hb] using ih values

/-- A name in an equally long zip always has a first matching value. -/
private theorem lookupZipSome (names : List MlString) (values : List InferT)
    (key : MlString) (hlen : names.length = values.length) (hmem : key ∈ names) :
    ∃ value, (names.zip values).lookup key = some value := by
  induction names generalizing values with
  | nil => simp at hmem
  | cons name names ih =>
    cases values with
    | nil => simp at hlen
    | cons value values =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.mem_cons] at hmem
      by_cases heq : key = name
      · subst key
        exact ⟨value, by simp⟩
      · have hb : (key == name) = false := by simp [heq]
        obtain ⟨v, hv⟩ := ih values hlen (hmem.resolve_left heq)
        exact ⟨v, by simpa [List.lookup, hb] using hv⟩

mutual
/-- Structural induction for conversion after named substitution. -/
private theorem convertTSubstType (t : SemanticT) (names : List MlString)
    (values : List InferT) (hlen : names.length = values.length)
    (h : checkFreevars 0 names t = true) :
    convertT (Infer.inferTypeSubst (names.zip values) t) =
      typeSubst (HolFiniteMapExact.alistToFmap (names.zip (values.map convertT))) t := by
  cases t with
  | var name =>
    have hmem : name ∈ names := by simpa [checkFreevars] using h
    obtain ⟨value, found⟩ := lookupZipSome names values name hlen hmem
    simp [Infer.inferTypeSubst, typeSubst, lookupAlistMap, lookupZipMap, found]
  | varDb n => simp [checkFreevars] at h
  | app ts tc =>
    have hl : checkFreevarsList 0 names ts = true := by simpa [checkFreevars] using h
    simp [Infer.inferTypeSubst, typeSubst, convertT, convertTSubstList ts names values hlen hl]
termination_by sizeOf t

/-- List recursion for conversion after named substitution. -/
private theorem convertTSubstList (ts : List SemanticT) (names : List MlString)
    (values : List InferT) (hlen : names.length = values.length)
    (h : checkFreevarsList 0 names ts = true) :
    convertTList (Infer.inferTypeSubstList (names.zip values) ts) =
      typeSubstList (HolFiniteMapExact.alistToFmap (names.zip (values.map convertT))) ts := by
  cases ts with
  | nil => simp [convertTList, Infer.inferTypeSubstList, typeSubstList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at h
    simp [convertTList, Infer.inferTypeSubstList, typeSubstList,
      convertTSubstType t names values hlen h.1, convertTSubstList ts names values hlen h.2]
termination_by sizeOf ts
end

/-- Named substitution commutes with conversion on types and type lists. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "convert_t_subst"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem convertTSubst :
    (∀ (t : SemanticT) (names : List MlString) (values : List InferT),
      names.length = values.length ∧ checkFreevars 0 names t = true →
      convertT (Infer.inferTypeSubst (names.zip values) t) =
        typeSubst (HolFiniteMapExact.alistToFmap (names.zip (values.map convertT))) t) ∧
    (∀ (ts : List SemanticT) (names : List MlString) (values : List InferT),
      names.length = values.length ∧ (∀ t ∈ ts, checkFreevars 0 names t = true) →
      (ts.map (Infer.inferTypeSubst (names.zip values))).map convertT =
        ts.map (typeSubst (HolFiniteMapExact.alistToFmap (names.zip (values.map convertT))))) := by
  constructor
  · intro t names values h
    exact convertTSubstType t names values h.1 h.2
  · intro ts names values h
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [convertTSubstType t names values h.1 h.2.1, ih ⟨h.1, h.2.2⟩]

end Flapjack.Compiler.Inference.EnvRel
