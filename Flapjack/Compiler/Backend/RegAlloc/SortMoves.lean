import Flapjack.HolRef
import Flapjack.Basis.Pure.MlList

namespace Flapjack.RegAlloc

/-- Descending priority sort over arbitrary payloads. The imported native
`MlList.sort` is the source-reviewed mllist sorting operation; its external
mergesort helpers are untagged and are not independently pinned by this tag. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "sort_moves_def"]
def sortMoves {α : Type} (moves : List (Nat × α)) : List (Nat × α) :=
  Basis.Pure.MlList.sort (fun left right => left.1 > right.1) moves

/-- Literal priority merge, including its behavior on unsorted inputs.
Equal priorities select the left head. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "smerge_def"]
def smerge {α : Type} : List (Nat × α) → List (Nat × α) → List (Nat × α)
  | [], ys => ys
  | xs, [] => xs
  | (p, m) :: xs, (q, n) :: ys =>
      if p ≥ q then (p, m) :: smerge xs ((q, n) :: ys)
      else (q, n) :: smerge ((p, m) :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Membership of the literal merge requires no sorting or distinctness
premise. The free HOL element is universally quantified. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "MEM_smerge"]
theorem memSmerge {α : Type} (x : Nat × α) (xs ys : List (Nat × α)) :
    x ∈ smerge xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  fun_induction smerge xs ys <;>
    simp_all [List.mem_cons, or_assoc, or_comm, or_left_comm]

end Flapjack.RegAlloc
