module

public import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
public import Flapjack.Misc.Sptree.ToAList
public import Flapjack.Misc.Option

@[expose] public section

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Original generic reconciliation move-list rewrite. HOL payloads are
arbitrary inhabited types; THE NONE remains the opaque library value. No
lookup-success/domain/distinctness premise is added. Nonempty alpha renders
HOL type inhabitance; DecidableEq alpha supplies lawful classical equality
for filtering, available for any type, not an added BEq law. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_moves_eq"
  (total_function_inhabitants := [α])]
theorem ssaReconcileMovesEq {α : Type} [Nonempty α] [DecidableEq α]
    (m : Spt α) (f : Nat → α) :
    ∀ (names : List Nat),
      (((names.map fun v => match sptLookup v m with
          | none => []
          | some cv => [(f v, cv)]).flatten).filter
          (fun (a, b) => decide (a ≠ b))) =
      ((names.filter fun v => match sptLookup v m with
          | none => false
          | some cv => decide (f v ≠ cv)).map
          (fun v => (f v, holThe (sptLookup v m)))) := by
  intro names
  induction names with
  | nil => rfl
  | cons v names ih =>
      cases hlook : sptLookup v m with
      | none => simpa [hlook] using ih
      | some cv =>
          by_cases hne : f v ≠ cv
          · simpa [hlook, hne, holThe] using (congrArg (List.cons (f v, cv)) ih)
          · simpa [hlook, hne] using ih

/-- Original unconditional distinctness of filtered native name keys. The
name-set payload remains arbitrary; current/target register maps are native Nat
maps as required by option_lookup. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_filtered_all_distinct"]
theorem ssaReconcileFilteredAllDistinct {α : Type}
    (curSSA tgtSSA : Spt Nat) (names : Spt α) :
    (((sptToAList names).map Prod.fst).filter fun v =>
      match sptLookup v curSSA with
      | none => false
      | some cv => decide (optionLookup tgtSSA v ≠ cv)).Nodup := by
  exact (sptAllDistinctMapFstToAList names).filter _

/-- Exact HOL `toAList_not_empty` (`word_allocProofScript.sml:822-827`): a
non-empty tree domain produces a non-empty association list. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "toAList_not_empty"]
theorem toAListNotEmpty {α : Type} (tree : Spt α)
    (h : sptDomain tree ≠ fun _ => False) : sptToAList tree ≠ [] := by
  intro hemp
  apply h
  funext key
  apply propext
  constructor
  · intro hs
    have hs' : (sptLookup key tree).isSome = true := hs
    obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp hs'
    have hmem := (sptMemToAList tree key value).mpr hvalue
    rw [hemp] at hmem
    simp at hmem
  · intro hf
    exact hf.elim

/-- Flapjack infrastructure for `ssa_reconcile_distinct_lemma`: filtering
mapped pairs by `f v ≠ g v` and keeping the first component is the same as
filtering the keys and mapping `f`. HOL proves the same rewrite inline. -/
private theorem filterPairFstMap {α β : Type} [DecidableEq α] (L : List β) (f g : β → α) :
    (List.map Prod.fst (List.filter (fun p : α × α => decide (p.1 ≠ p.2))
      (List.map (fun v => (f v, g v)) L))) =
      List.map f (List.filter (fun v => decide (f v ≠ g v)) L) := by
  induction L with
  | nil => rfl
  | cons a as ih =>
      by_cases h : f a = g a
      · have hp : decide ((f a, g a).1 ≠ (f a, g a).2) = false := by simp [h]
        simp only [List.map_cons, List.filter_cons, hp]
        exact ih
      · have hp : decide ((f a, g a).1 ≠ (f a, g a).2) = true := by simp [h]
        simp only [List.map_cons, List.filter_cons, hp, if_true, List.map]
        rw [ih]

/-- Flapjack infrastructure for `ssa_reconcile_distinct_lemma`: mapping a
list through a function injective on that list preserves distinctness. HOL
uses `ALL_DISTINCT_MAP_INJ` for the same step. -/
private theorem nodup_map_of_injOn {α β : Type} (l : List α) (f : α → β)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (hnd : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have hcons := List.nodup_cons.mp hnd
      have hninj : ∀ x ∈ as, ∀ y ∈ as, f x = f y → x = y :=
        fun x hx y hy hxy =>
          hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy
      refine List.nodup_cons.mpr ⟨?_, ih hninj hcons.2⟩
      intro hmem
      obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
      have hba : b = a := hinj b (List.mem_cons_of_mem a hb) a (by simp) hfb
      exact hcons.1 (hba ▸ hb)

/-- Exact HOL `ssa_reconcile_distinct_lemma`
(`word_allocProofScript.sml:6459-6485`): an injection on the tree domain makes
the reconciled source names distinct. HOL `FST`/`FILTER` are Lean
`Prod.fst`/`List.filter` with the Boolean test written `decide`; classical
equality on the payload is the lawful rendering of HOL's total equality. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_distinct_lemma"]
theorem ssaReconcileDistinctLemma {α β : Type} [DecidableEq α]
    (f g : Nat → α) (ns : Spt β)
    (h : ∀ x y, sptDomain ns x → sptDomain ns y → f x = f y → x = y) :
    (List.map Prod.fst (List.filter (fun p : α × α => decide (p.1 ≠ p.2))
      (List.map (fun v => (f v, g v)) (List.map Prod.fst (sptToAList ns))))).Nodup := by
  have hlist :
      List.map Prod.fst (List.filter (fun p : α × α => decide (p.1 ≠ p.2))
        (List.map (fun v => (f v, g v)) (List.map Prod.fst (sptToAList ns)))) =
      List.map f (List.filter (fun v => decide (f v ≠ g v))
        (List.map Prod.fst (sptToAList ns))) :=
    filterPairFstMap _ f g
  rw [hlist]
  apply nodup_map_of_injOn
  · intro x hx y hy hxy
    exact h x y ((sptMemMapFstToAList ns x).mp (List.mem_filter.mp hx).1)
      ((sptMemMapFstToAList ns y).mp (List.mem_filter.mp hy).1) hxy
  · exact (sptAllDistinctMapFstToAList ns).filter _

/-- Exact HOL `ssa_reconcile_filtered_in_dom`
(`word_allocProofScript.sml:6510-6523`): a name surviving the reconciliation
filter is in the tree domain and its current register differs from the target
one. HOL `THE` is the tagged `holThe`; the filter test is the same Boolean
form as the sibling `ssa_reconcile_filtered_all_distinct` port. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_filtered_in_dom"]
theorem ssaReconcileFilteredInDom {α : Type} (curSSA tgtSSA : Spt Nat)
    (names : Spt α) (v : Nat)
    (h : v ∈ (((sptToAList names).map Prod.fst).filter fun v =>
      match sptLookup v curSSA with
      | none => false
      | some cv => decide (optionLookup tgtSSA v ≠ cv))) :
    sptDomain names v ∧ ∃ cv, sptLookup v curSSA = some cv ∧
      optionLookup tgtSSA v ≠ cv ∧ holThe (sptLookup v curSSA) = cv := by
  have hmem := (List.mem_filter.mp h).1
  have hpred := (List.mem_filter.mp h).2
  refine ⟨(sptMemMapFstToAList names v).mp hmem, ?_⟩
  cases hl : sptLookup v curSSA with
  | none => simp [hl] at hpred
  | some cv =>
      refine ⟨cv, rfl, ?_, ?_⟩
      · simpa [hl] using hpred
      · simp [holThe]

end Flapjack.Compiler.Backend.WordAlloc
