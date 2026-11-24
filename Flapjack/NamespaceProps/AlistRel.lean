module

public import Flapjack.NamespaceProps.AlistLookup

@[expose] public section

/-! Association-list relations restricted to a key list. -/
namespace Flapjack.NamespaceHOL

/-- Original `alist_rel_restr_def`: every listed key is found in both
association lists with related values. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "alist_rel_restr_def"]
def alistRelRestr {K V W : Type} [DecidableEq K] (R : K → V → W → Prop)
    (l1 : List (K × V)) (l2 : List (K × W)) : List K → Prop
  | [] => True
  | k :: keys =>
      match l1.lookup k with
      | none => False
      | some v1 =>
        match l2.lookup k with
        | none => False
        | some v2 => R k v1 v2 ∧ alistRelRestr R l1 l2 keys

/-- The restricted relation is exactly universal relatedness over the listed
keys. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "alist_rel_restr_thm"]
theorem alistRelRestr_thm {K V W : Type} [DecidableEq K]
    (R : K → V → W → Prop) (e1 : List (K × V)) (e2 : List (K × W)) (keys : List K) :
    alistRelRestr R e1 e2 keys ↔
      ∀ k, k ∈ keys → ∃ v1 v2, e1.lookup k = some v1 ∧ e2.lookup k = some v2 ∧ R k v1 v2 := by
  induction keys with
  | nil => simp [alistRelRestr]
  | cons k keys ih =>
    simp only [alistRelRestr, List.mem_cons, forall_eq_or_imp]
    cases h1 : e1.lookup k with
    | none => simp
    | some v1 =>
      cases h2 : e2.lookup k with
      | none => simp
      | some v2 => simp [ih]

/-- Original `alistSub_def`: the restricted relation over every key of the
first list. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "alistSub_def"]
def alistSub {K V W : Type} [DecidableEq K] (R : K → V → W → Prop)
    (l1 : List (K × V)) (l2 : List (K × W)) : Prop :=
  alistRelRestr R l1 l2 (l1.map Prod.fst)

/-- The association-list sub-relation depends only on the lists and on the
relation values at the looked-up entries. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "alistSub_cong"]
theorem alistSub_cong {K V W : Type} [DecidableEq K]
    (l1 : List (K × V)) (l2 : List (K × W)) (l1' : List (K × V)) (l2' : List (K × W))
    (R R' : K → V → W → Prop)
    (premise : l1 = l1' ∧ l2 = l2' ∧
      ∀ n x y, l1'.lookup n = some x → l2'.lookup n = some y → (R n x y ↔ R' n x y)) :
    alistSub R l1 l2 ↔ alistSub R' l1' l2' := by
  obtain ⟨sameFirst, sameSecond, relation⟩ := premise
  subst sameFirst
  subst sameSecond
  have pointwise : ∀ keys, alistRelRestr R l1 l2 keys ↔ alistRelRestr R' l1 l2 keys := by
    intro keys
    induction keys with
    | nil => simp [alistRelRestr]
    | cons k keys ih =>
      simp only [alistRelRestr]
      cases h1 : l1.lookup k with
      | none => simp
      | some v1 =>
        cases h2 : l2.lookup k with
        | none => simp
        | some v2 => simp [ih, relation k v1 v2 h1 h2]
  simp only [alistSub]
  exact pointwise (l1.map Prod.fst)

end Flapjack.NamespaceHOL
