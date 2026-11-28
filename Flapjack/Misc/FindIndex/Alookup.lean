module

public import Flapjack.Misc.FindIndex
public import Flapjack.Misc.FindIndex.ShiftZero
public import Flapjack.Misc.ListEl

@[expose] public section

namespace Flapjack.Misc

/-- Original `ALOOKUP_find_index_NONE`: when the association list has no entry
for the key, searching the projected key list fails too. HOL's `ALOOKUP` is
`List.lookup` and `MAP FST` is `List.map Prod.fst`. -/
@[hol "cakeml/misc/miscScript.sml" "ALOOKUP_find_index_NONE"]
theorem lookup_findIndex_none {α β : Type} [DecidableEq β] (env : List (β × α))
    (k : β) :
    ∀ m : Nat, env.lookup k = none → findIndex k (env.map Prod.fst) m = none := by
  induction env with
  | nil =>
    intro m _
    simp [findIndex]
  | cons pair rest ih =>
    intro m h
    obtain ⟨k', v⟩ := pair
    by_cases same : k' = k
    · have hbeq : (k == k') = true := by simp [same]
      simp [List.lookup, hbeq] at h
    · have hbeq : (k == k') = false := by simp [Ne.symm same]
      simp only [List.lookup, hbeq, List.map_cons, findIndex, if_neg same] at h ⊢
      exact ih (m + 1) h

/-- Original `ALOOKUP_find_index_SOME`: a lookup hit is a first-match hit at the
same index, with the same value. -/
@[hol "cakeml/misc/miscScript.sml" "ALOOKUP_find_index_SOME" 1148
  (total_function_inhabitants := [α, β])]
theorem alookupFindIndexSome {α β : Type} [DecidableEq β] [Nonempty α] [Nonempty β]
    (env : List (β × α)) (k : β) (v : α) (h : List.lookup k env = some v) :
    ∃ i, findIndex k (env.map Prod.fst) 0 = some i ∧ i < env.length ∧ v = (holEl i env).2 := by
  induction env with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.lookup_cons] at h
    cases hbeq : (k == a) with
    | true =>
      have hka : k = a := by simpa [beq_iff_eq] using hbeq
      simp only [hbeq, Option.some.injEq] at h
      subst hka
      subst h
      exact ⟨0, by simp [Flapjack.Misc.findIndex.eq_def], by simp, rfl⟩
    | false =>
      simp only [hbeq] at h
      obtain ⟨i, hi, hlt, hv⟩ := ih h
      have hshift := findIndexShiftZero (List.map Prod.fst rest) k 1
      refine ⟨i + 1, ?_, ?_, ?_⟩
      · rw [List.map_cons]
        simp only [Flapjack.Misc.findIndex]
        rw [if_neg]
        · rw [hshift, hi]
          rfl
        · intro heq
          exact absurd heq.symm (by simpa [beq_iff_eq] using hbeq)
      · simp only [List.length_cons]
        omega
      · exact hv

end Flapjack.Misc
