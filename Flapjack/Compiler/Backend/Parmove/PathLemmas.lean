import Flapjack.Compiler.Backend.Parmove.Invariants
import Flapjack.Compiler.Backend.Parmove.Semantics
import Flapjack.Misc.ListEl

/-!
# parmove path lemmas

`path_imp_mem`, `path_imp_mem2` and `NoRead_path` of
`cakeml/compiler/backend/reg_alloc/parmoveScript.sml` (81-117, all `[local]`):
along a path of moves every source but the last is the destination of the next
move. HOL's local overload `NoRead μ dn` is `¬MEM dn (MAP SND μ)`.
-/

namespace Flapjack.Compiler.Backend.Parmove

open Flapjack

/-- Exact HOL `path_imp_mem` (`parmoveScript.sml:81-87`). HOL's free `x y` are
implicit; `NULL y` is `y = []`. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_imp_mem"]
theorem path_imp_mem {α : Type} {x : α × α} {y : List (α × α)} :
    path (x :: y) → ¬ y = [] → x.2 ∈ y.map Prod.fst := by
  intro h hy
  rcases y with _ | ⟨⟨b, a⟩, p⟩
  · exact absurd rfl hy
  · rcases x with ⟨c, b'⟩
    simp only [path] at h
    simp [h.1]

/-- Exact HOL `path_imp_mem2` (`parmoveScript.sml:89-100`). HOL's free `x` is
implicit; `LAST` is the `holLast` port. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_imp_mem2"]
theorem path_imp_mem2 {α : Type} [Nonempty α] {x : List (α × α)} :
    path x → ∀ y, y ∈ x.map Prod.snd ∧ y ≠ (holLast x).2 → y ∈ x.map Prod.fst := by
  induction x with
  | nil => intro _ y h; simp at h
  | cons h t ih =>
      intro hp y ⟨hm, hne⟩
      rcases t with _ | ⟨n, t⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hm
        exact absurd hm (by simpa [holLast] using hne)
      · rcases h with ⟨c, b'⟩
        rcases n with ⟨b, a⟩
        simp only [path] at hp
        simp only [List.map_cons, List.mem_cons] at hm ⊢
        rcases hm with rfl | hm
        · exact Or.inr (Or.inl hp.1.symm)
        · have := ih hp.2 y ⟨by simpa using hm, by simpa [holLast] using hne⟩
          simpa using Or.inr this

/-- Exact HOL `NoRead_path` (`parmoveScript.sml:102-117`). `HD`, `TL`, `LAST`
are `holHd`, `List.tail` and `holLast`; `windmill` is the tagged `windmill`. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "NoRead_path"]
theorem NoRead_path {α : Type} [Nonempty α] :
    ∀ σ : List (α × α), path σ ∧ windmill σ ∧ σ.length ≥ 2 ∧
      (holHd σ).1 ≠ (holLast σ).2 → (holHd σ).1 ∉ σ.tail.map Prod.snd := by
  intro σ ⟨hp, hw, hl, hne⟩ hmem
  rcases σ with _ | ⟨⟨d, s⟩, t⟩
  · simp at hl
  simp only [holHd, List.tail_cons] at hne hmem
  have ht : t ≠ [] := by rintro rfl; simp at hl
  have hlast : holLast ((d, s) :: t) = holLast t := by
    rcases t with _ | ⟨_, _⟩
    · exact absurd rfl ht
    · simp [holLast]
  rw [hlast] at hne
  have hpt := path_tail t (d, s) hp
  have hfst := path_imp_mem2 hpt d ⟨hmem, hne⟩
  simp only [windmill, List.map_cons, List.nodup_cons] at hw
  exact hw.1 hfst

end Flapjack.Compiler.Backend.Parmove
